#!/usr/bin/env bash
# Installs elan and the toolchain `lean-toolchain` names, retrying the downloads.
#
# Lean's release server answers the occasional 504, so without retries any blip fails the job.
# Every other toolchain the projects name is this one, so nothing else gets downloaded later.
#
# Both steps are skipped when there is nothing to do: CI restores `~/.elan` from its cache, which
# leaves elan installed and, unless the toolchain changed, the toolchain too.
#
# In a workflow, puts elan on the `PATH` of the steps that follow.
set -euo pipefail

if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl --retry 5 --retry-delay 10 --retry-all-errors -sSfL \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
  sh elan-init.sh -y --default-toolchain none --no-modify-path
  rm elan-init.sh
fi
if [ -n "${GITHUB_PATH:-}" ]; then
  echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
fi

toolchain=$(tr -d '[:space:]' < lean-toolchain)
attempts=5
for attempt in $(seq 1 $attempts); do
  if "$HOME/.elan/bin/elan" toolchain install "$toolchain"; then
    break
  fi
  if [ "$attempt" -eq "$attempts" ]; then
    echo "::error::could not install $toolchain after $attempts attempts"
    exit 1
  fi
  echo "installing $toolchain failed (attempt $attempt/$attempts), retrying in $((attempt * 20))s"
  sleep $((attempt * 20))
done

# elan picks the toolchain from `lean-toolchain`, so this checks the one just installed answers
"$HOME/.elan/bin/lean" --version
"$HOME/.elan/bin/lake" --version
