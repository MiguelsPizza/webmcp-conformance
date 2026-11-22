// Run exported WPT tests (tools/export-wpt.cjs) in Playwright, the way wptrunner would: served
// over http://localhost (a secure context) next to WPT's /resources/testharness.js, with the
// polyfill injected before the page's scripts for a polyfill target.
//
//   node tools/run-wpt-export.cjs <wpt checkout> <target> [dir=wpt-export] [--json <file>]
//
// <target> is polyfill:<path to dist/polyfill.js>, chromium, or chromium:<path to chrome>, as
// for harness/run.cjs. Prints each test's status; exits non-zero if any test didn't pass.
const { chromium } = require("playwright");
const { spawnSync } = require("node:child_process");
const fs = require("node:fs");
const http = require("node:http");
const path = require("node:path");

const args = process.argv.slice(2);
const jsonAt = args.indexOf("--json");
const jsonOut = jsonAt >= 0 ? args.splice(jsonAt, 2)[1] : null;
const [wpt, target, dirArg = path.join(__dirname, "..", "wpt-export")] = args;
const dir = path.resolve(dirArg);
if (!wpt || !target) throw new Error("usage: node tools/run-wpt-export.cjs <wpt checkout> <target> [dir] [--json <file>]");
const [kind, ...rest] = target.split(":");
const targetArg = rest.join(":");
const polyfill = kind === "polyfill" ? fs.readFileSync(targetArg, "utf8") : null;
const launchOptions =
  kind === "chromium"
    ? { args: ["--enable-blink-features=WebMCP"], ...(targetArg ? { executablePath: targetArg } : {}) }
    : {};

// What a runner adds to testharnessreport.js: hand the results to the runner when done.
const report = `
add_completion_callback((tests, status) => {
  window.__wpt = { status: status.status, message: status.message,
    tests: tests.map((t) => ({ name: t.name, status: t.status, message: t.message })) };
});`;
const files = fs.readdirSync(dir).filter((f) => f.endsWith(".html")).sort();
const server = http.createServer((req, res) => {
  const url = decodeURIComponent(new URL(req.url, "http://localhost").pathname);
  let body = null;
  if (url.startsWith("/resources/")) {
    const file = path.join(wpt, "resources", path.basename(url));
    if (fs.existsSync(file)) body = fs.readFileSync(file, "utf8") + (url.endsWith("/testharnessreport.js") ? report : "");
  } else if (url.startsWith("/webmcp/conformance/")) {
    const file = path.join(dir, url.slice("/webmcp/conformance/".length));
    if (file.startsWith(path.resolve(dir) + path.sep) && fs.existsSync(file) && fs.statSync(file).isFile()) {
      body = fs.readFileSync(file, "utf8");
    }
  }
  if (body === null) {
    res.writeHead(404).end();
    return;
  }
  const type = url.endsWith(".js") ? "text/javascript" : url.endsWith(".css") ? "text/css" : "text/html";
  res.writeHead(200, { "content-type": `${type}; charset=utf-8` }).end(body);
});

const STATUS = ["PASS", "FAIL", "TIMEOUT", "NOTRUN", "PRECONDITION_FAILED"];
const HARNESS = ["OK", "ERROR", "TIMEOUT", "PRECONDITION_FAILED"];
(async () => {
  await new Promise((r) => server.listen(0, "127.0.0.1", r));
  const origin = `http://localhost:${server.address().port}`;
  const browser = await chromium.launch(launchOptions);
  console.log(`target ${target}, browser ${browser.version()}`);
  const results = [];
  for (const f of files) {
    const page = await browser.newPage();
    if (polyfill) await page.addInitScript(polyfill);
    await page.goto(`${origin}/webmcp/conformance/${f}`);
    const r = await page.waitForFunction(() => window.__wpt, null, { timeout: 30000 }).then((h) => h.jsonValue())
      .catch(() => ({ status: 2, message: "no result within 30s", tests: [] }));
    await page.close();
    const tests = r.tests.map((t) => ({ name: t.name, status: STATUS[t.status], message: t.message }));
    const passed = r.status === 0 && tests.length > 0 && tests.every((t) => t.status === "PASS");
    results.push({ file: f, harness: HARNESS[r.status], harnessMessage: r.message ?? null, passed, tests });
    console.log(`${passed ? "PASS" : "FAIL"} ${f}`);
    if (r.status !== 0) console.log(`     harness ${HARNESS[r.status]}: ${r.message}`);
    for (const t of tests) if (t.status !== "PASS") console.log(`     ${t.status}: ${t.message}`);
  }
  const passed = results.filter((r) => r.passed).length;
  console.log(`${passed} of ${results.length} tests pass`);
  if (jsonOut) {
    // A polyfill path relative to its git checkout, named after the checkout's folder, as the
    // harness's results files show it.
    let shown = target;
    if (polyfill) {
      const top = spawnSync("git", ["-C", path.dirname(path.resolve(targetArg)), "rev-parse", "--show-toplevel"], { encoding: "utf8" });
      const t = top.status === 0 ? top.stdout.trim() : null;
      shown = `polyfill:${t ? path.join(path.basename(t), path.relative(t, path.resolve(targetArg))) : path.basename(targetArg)}`;
    }
    fs.writeFileSync(jsonOut, JSON.stringify({ target: shown, browser: browser.version(), date: new Date().toISOString(), results }, null, 2) + "\n");
  }
  await browser.close();
  server.close();
  process.exitCode = passed === results.length ? 0 : 1;
})();
