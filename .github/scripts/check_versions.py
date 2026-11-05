"""Checks that the Lake projects sharing `.lake/packages` agree on what they share.

The root, the manual (`CvcManual`) and the generated API reference project (`.lake/docbuild`) use
one packages directory. A package two of them require must therefore be at the same revision in
both, or each build checks its own revision out in turn and rebuilds; and the manual must be on the
root's toolchain, with Verso pinned to that version. None of this fails a build by itself, so it is
checked here instead, before anything is built.

Usage, from the repository root: `python3 .github/scripts/check_versions.py MANIFEST...`, each
argument a `lake-manifest.json`. The toolchain and Verso checks always run.
"""

import json
import pathlib
import sys
import tomllib

errors: list[str] = []


def fail(message: str) -> None:
    errors.append(message)
    print(f"::error::{message}")


def toolchain(path: str) -> str:
    return pathlib.Path(path).read_text().strip()


root_toolchain = toolchain("lean-toolchain")
manual_toolchain = toolchain("CvcManual/lean-toolchain")
if manual_toolchain != root_toolchain:
    fail(f"the manual is on `{manual_toolchain}`, the library on `{root_toolchain}`")

# Verso tags one revision per Lean release, named after it
version = root_toolchain.split(":", 1)[-1]
manual_config = tomllib.loads(pathlib.Path("CvcManual/lakefile.toml").read_text())
verso = next((r for r in manual_config.get("require", []) if r.get("name") == "verso"), None)
if verso is None:
    fail("the manual does not require Verso")
elif verso.get("rev") != version:
    fail(f"the manual pins Verso at `{verso.get('rev')}`, the toolchain is `{version}`")

# package name -> (revision, manifest it was read from), for every git package seen so far
seen: dict[str, tuple[str, str]] = {}
for manifest in sys.argv[1:]:
    packages = json.loads(pathlib.Path(manifest).read_text())["packages"]
    for package in packages:
        if package.get("type") != "git":
            continue
        name = package["name"].strip("«»")
        rev = package["rev"]
        if name in seen and seen[name][0] != rev:
            other_rev, other = seen[name]
            fail(f"`{name}` is at {rev[:10]} in {manifest} but at {other_rev[:10]} in {other}")
        seen.setdefault(name, (rev, manifest))

if errors:
    sys.exit(1)
print(f"versions agree: {root_toolchain}, Verso {version}, {len(seen)} shared-directory packages")
