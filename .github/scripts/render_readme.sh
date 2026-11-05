#!/usr/bin/env bash
# Renders a Markdown file as a standalone HTML page, through GitHub's own Markdown renderer.
#
# Usage: render_readme.sh INPUT.md OUTPUT.html
#
# Needs an authenticated `gh` (`GH_TOKEN`). In a workflow, `GITHUB_REPOSITORY` gives the renderer
# the repository as context, so that references to issues and commits resolve.
#
# GitHub prefixes the id of every heading with `user-content-` and relies on JavaScript to map
# `#documentation` to it; there is no such script here, so the prefix is removed instead.
set -euo pipefail

input=$1
output=$2

args=(-X POST /markdown -f mode=gfm -F "text=@$input")
if [ -n "${GITHUB_REPOSITORY:-}" ]; then
  args+=(-f "context=$GITHUB_REPOSITORY")
fi
body=$(gh api "${args[@]}")

mkdir -p "$(dirname "$output")"
{
  cat <<'HTML'
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>cvc.lean</title>
<style>
  :root { color-scheme: light dark; }
  body {
    max-width: 50rem; margin: 2rem auto; padding: 0 1rem;
    font-family: system-ui, sans-serif; line-height: 1.5;
  }
  pre { padding: 1rem; overflow-x: auto; border-radius: 6px; background: #8881; }
  code { font-size: 0.9em; }
  /* the anchor carries the heading's id, so only its link icon is hidden: a link cannot scroll to
     an element that is not displayed */
  .anchor svg { display: none; }
</style>
</head>
<body>
HTML
  printf '%s\n' "$body" | sed 's/id="user-content-/id="/g'
  printf '%s\n' '</body>' '</html>'
} > "$output"
