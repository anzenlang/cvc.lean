#!/usr/bin/env bash
# Checks a release the way a user gets it: a fresh project requires cvc.lean at the release's tag.
#
# The project builds an executable using cvc5 — which links everything the lean-cvc5 bundle carries
# — and the check then asserts that
# - the release's lean-cvc5 bundle was restored;
# - lean-cvc5 fetched nothing: neither its own build archive nor cvc5's static release;
# - nothing of lean-cvc5 was rebuilt;
# - the executable runs.
#
# A command lean-cvc5 really runs names this project's directory, while one replayed from the
# bundle's traces names the machine that built the bundle: that is how the log tells them apart.
#
# Usage: check_release.sh <repository URL> <tag>, from the repository's root, whose `lean-toolchain`
# the project uses.
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: $0 <repository URL> <tag>" >&2
  exit 2
fi
repo=$1
tag=$2

fail() {
  echo "::error::$1"
  exit 1
}

# the physical path, which is what Lake prints
dir=$(cd "$(mktemp -d)" && pwd -P)
cp lean-toolchain "$dir/"
cat > "$dir/lakefile.toml" <<EOF
name = "check"
defaultTargets = ["check"]

[[require]]
name = "cvc"
git = "$repo"
rev = "$tag"

[[lean_exe]]
name = "check"
root = "Check"
EOF
cat > "$dir/Check.lean" <<'EOF'
import Cvc.Srt

def main : IO Unit := do
  IO.println (← Cvc.Env.runIO do return s!"cvc5 answers: {← Cvc.Srt.int}")
EOF

cd "$dir"
echo "checking $repo at $tag in $dir"
lake update
log=$dir/build.log
if ! lake build -v > "$log" 2>&1; then
  tail -n 60 "$log"
  fail "building a project requiring $tag failed"
fi

grep -E "restored lean-cvc5 from" "$log" || fail "the lean-cvc5 bundle was not restored"
if grep -E '^trace: \.> curl' "$log" | grep -F "$dir"; then
  fail "lean-cvc5 downloaded files despite the bundle"
fi
if grep -F "$dir" .lake/packages/cvc5/.lake/build/cvc5Enums.trace; then
  fail "lean-cvc5 fetched cvc5 again despite the bundle"
fi
if grep -E '\] Built cvc5' "$log"; then
  fail "lean-cvc5 was rebuilt despite the bundle"
fi

answer=$(lake exe check)
echo "$answer"
[ "$answer" = "cvc5 answers: Int" ] || fail "the executable answered \`$answer\`"
echo "$tag checks out"
