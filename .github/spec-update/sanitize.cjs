// Neutralises references in model-written PR text so an update PR never pings anyone or adds
// "mentioned this" entries to another repo's issues and PRs: @-mentions, owner/repo#123,
// owner/repo@sha, #123, GH-123, and links to GitHub issues, PRs, commits or discussions are
// wrapped in code spans, which GitHub neither links nor cross-references. Existing code is left as is.
// Titles and commit messages don't render code spans reliably, so there the markers are dropped.
//   node sanitize.cjs <file>            rewrites a Markdown file in place
//   node sanitize.cjs --title <file>    rewrites a one-line title in place
const fs = require("node:fs");
const title = process.argv[2] === "--title";
const file = process.argv[title ? 3 : 2];
const ref = new RegExp(
  [
    String.raw`https?://(?:www\.)?github\.com/[^\s)>\]]+`,
    String.raw`[\w.-]+/[\w.-]+[#@][\w]+`,
    String.raw`(?<![\w&/])@[A-Za-z0-9][\w-]*(?:/[\w.-]+)?`,
    String.raw`(?<![\w&/])(?:GH-|#)\d+\b`,
  ].join("|"),
  "g",
);
const text = fs.readFileSync(file, "utf8");
if (title) {
  const plain = text
    .split("\n")[0]
    .replace(/https?:\/\/\S+/g, "")
    .replace(/[\w.-]+\/[\w.-]+(?=[#@])/g, "")
    .replace(/[#@`]/g, "")
    .replace(/\s+/g, " ")
    .trim();
  fs.writeFileSync(file, plain + "\n");
  process.exit(0);
}
const out = text
  .split(/(```[\s\S]*?```|`[^`\n]*`)/)
  .map((part, i) => (i % 2 ? part : part.replace(ref, (m) => "`" + m + "`")))
  .join("");
fs.writeFileSync(file, out);
