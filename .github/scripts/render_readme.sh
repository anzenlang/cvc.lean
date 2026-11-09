#!/usr/bin/env bash
# Renders the README as the site's front page, through GitHub's own Markdown renderer.
#
# Usage: render_readme.sh INPUT.md OUTPUT.html TAG
#
# Run from the repository's root. The page is the rendered README under a header naming the release
# `TAG` and the Lean version `lean-toolchain` names, with links to the manual, the API reference and
# the repository. `GITHUB_REPOSITORY` names the repository (upstream's when unset), which also gives
# the renderer the context it resolves references to issues and commits in.
#
# Needs an authenticated `gh` (`GH_TOKEN`). GitHub prefixes the id of every heading with
# `user-content-` and relies on JavaScript to map `#documentation` to it; there is no such script
# here, so the prefix is removed instead.
set -euo pipefail

input=$1
output=$2
tag=$3

repository=${GITHUB_REPOSITORY:-anzenlang/cvc.lean}
repo_url="https://github.com/$repository"
# `leanprover/lean4:v4.35.0` → `4.35.0`
lean=$(tr -d '[:space:]' < lean-toolchain)
lean=${lean##*:v}

body=$(gh api -X POST /markdown -f mode=gfm -f "context=$repository" -F "text=@$input")

mkdir -p "$(dirname "$output")"
{
  cat <<'HTML'
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>cvc.lean</title>
<link rel="stylesheet"
  href="https://cdn.jsdelivr.net/npm/github-markdown-css@5.5.1/github-markdown.min.css">
<style>
  :root { color-scheme: light dark; --bar: #f6f8fa; --line: #d0d7de; --link: #0969da; }
  @media (prefers-color-scheme: dark) {
    :root { --bar: #161b22; --line: #30363d; --link: #4493f8; }
  }
  body { margin: 0; background: Canvas; }
  .bar {
    position: sticky; top: 0; z-index: 1; display: flex; flex-wrap: wrap; align-items: center;
    justify-content: space-between; gap: 0.5rem 1rem;
    padding: 0.75rem max(1rem, calc((100vw - 50rem) / 2));
    background: var(--bar); border-bottom: 1px solid var(--line);
    font-family: system-ui, sans-serif;
  }
  .bar .left { display: flex; flex-wrap: wrap; align-items: baseline; gap: 0.6rem; }
  .bar .brand { font-weight: 600; font-size: 1.15rem; color: CanvasText; text-decoration: none; }
  .bar .release { font-size: 0.9rem; color: var(--link); text-decoration: none; }
  .bar .lean { font-size: 0.9rem; opacity: 0.7; }
  .bar nav { display: flex; flex-wrap: wrap; gap: 1.25rem; }
  .bar nav a { color: var(--link); text-decoration: none; font-weight: 500; }
  .bar a:hover { text-decoration: underline; }
  .markdown-body { box-sizing: border-box; max-width: 50rem; margin: 0 auto; padding: 2rem 1rem; }
</style>
</head>
<body>
HTML
  cat <<HTML
<header class="bar">
  <span class="left">
    <a class="brand" href="./">cvc.lean</a>
    <span><a class="release" href="$repo_url/releases/tag/$tag">latest release: $tag</a><span class="lean">, for Lean $lean</span></span>
  </span>
  <nav>
    <a href="manual/">Manual</a>
    <a href="api/Cvc.html">API reference</a>
    <a href="$repo_url">GitHub</a>
  </nav>
</header>
<main class="markdown-body">
HTML
  printf '%s\n' "$body" | sed 's/id="user-content-/id="/g'
  printf '%s\n' '</main>' '</body>' '</html>'
} > "$output"
