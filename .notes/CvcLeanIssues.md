# Issues to open on cvc.lean

Drafts of issues for cvc.lean's own repository: work worth tracking in the open, each written to be
pasted there as is. An entry is the issue: a **Title:** line, then the body from its first section
down. Once an entry is filed its body gives way to the issue's link, and once that issue is closed
the entry goes.

This is not the list of things cvc.lean does not wrap, which is [MISSING.md](MISSING.md), nor of
designs deliberately not started, which is [TODO.md](TODO.md). Problems in cvc5, lean-cvc5 and Lean
themselves are in [Cvc5Issues.md](Cvc5Issues.md) and [LeanIssues.md](LeanIssues.md).

## 1. Windows CI

**Status: draft.** Its first blocker is entry 11 of [Cvc5Issues.md](Cvc5Issues.md), to file against
lean-cvc5 first: the body has a placeholder link to that issue.

**Title:** Build and test on Windows in CI

### Summary

CI builds and tests on Linux only, and releases carry lean-cvc5 bundles for Linux and macOS only.
lean-cvc5 builds and tests on Windows in its own CI, so cvc.lean could too, and covering Windows in
CI is the first step towards Windows releases.

A trial workflow, below, ran on `windows-latest`. The library builds, and every test passes but
`CvcTests.Srt`, which a lean-cvc5 bug breaks on Windows. The workflow was not merged, so as not to
put a failing check on every pull request.

### What the trial found

- `lake build` succeeds, in about two and a half minutes with nothing cached. That includes
  downloading cvc5's static release, so Lake's `curl` and `tar` work under the setup below.
- `lake test` fails `CvcTests.Srt` alone, on abstract sorts:

  ```
  [internal] cannot construct abstract type for kind UNDEFINED_SORT_KIND
  ```

  lean-cvc5's `termManager_mkAbstractSort`, in its `ffi/ffi.cpp`, reads its `SortKind` as a
  `uint16_t` while Lean passes a `uint8_t`, and the Windows x64 calling convention leaves the high
  byte undefined. So on Windows `Srt.any`, `Srt.abstract` and the sort of an abstract `Typ?` fail or
  work depending on the call. Reported as [a lean-cvc5 issue](TODO); the fix is one word.
- Whether an executable using the library links and runs is not known: the trial skipped that step
  after the failed test. Linking is where Linux had its own problem, lean-cvc5's cvc5 needing
  glibc 2.38, which `Cvc/glibc_compat.c` works around, so it deserves checking first.
- The glibc shim is linked on Linux only, so a Windows build compiles no C of its own.

### To do

- [ ] Get `mkAbstractSort` fixed in lean-cvc5 and move to a revision with the fix, or skip the
      abstract-sort tests on Windows until then, so that the check does not start out failing.
- [ ] Add the workflow, and see the executable link and run.
- [ ] Decide when it runs. The trial ran by hand and on pull requests to `main` only, since it is
      uncached and slower than the Linux job.
- [ ] Separately, Windows release bundles: `release.yml` has no Windows platform, and
      `.github/scripts/check_release.sh` would need adapting to Windows (`\r` in a program's output,
      Windows paths).

### The trial workflow

It uses lean-cvc5's own Windows CI environment: MSYS2's CLANG64, whose clang lean-cvc5 compiles its
`ffi.cpp` with when it builds from source, and Lean installed by `leanprover/lean-action`. The link
step builds an executable in a project sharing the repository's packages directory, so that the
library is not rebuilt against another checkout of lean-cvc5, and checks what it prints.

```yaml
name: Windows

# Builds and tests the library on Windows, and links an executable using it, which is where a
# platform's linking problems show.

on:
  workflow_dispatch:
  pull_request:
    branches: [main]

permissions:
  contents: read

concurrency:
  group: windows-${{ github.ref }}
  cancel-in-progress: true

jobs:
  build:
    runs-on: windows-latest
    timeout-minutes: 120
    defaults:
      run:
        shell: msys2 {0}
    steps:
      - name: Checkout
        uses: actions/checkout@v7
      - name: Install MSYS2
        uses: msys2/setup-msys2@v2
        with:
          msystem: CLANG64
          path-type: inherit
          install: mingw-w64-clang-x86_64-clang
      - name: Install Lean
        uses: leanprover/lean-action@v1
        with:
          auto-config: false
          use-github-cache: false
      - name: Build
        id: build
        run: lake build
      - name: Test
        run: lake test
      # after a failed test too: a failing test must not hide whether linking works
      - name: Link an executable using the library
        if: ${{ !cancelled() && steps.build.outcome == 'success' }}
        run: |
          repo=$(cygpath -m "$PWD")
          dir=$(mktemp -d)
          cp lean-toolchain "$dir/"
          # the repository's packages directory, so that the library is not rebuilt against another
          # checkout of lean-cvc5
          cat > "$dir/lakefile.toml" <<EOF
          name = "check"
          defaultTargets = ["check"]
          packagesDir = "$repo/.lake/packages"

          [[require]]
          name = "cvc"
          path = "$repo"

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
          lake build
          answer=$(lake exe check | tr -d '\r')
          echo "$answer"
          if [ "$answer" != "cvc5 answers: Int" ]; then
            echo "::error::the executable answered \`$answer\`"
            exit 1
          fi
```
