#!/usr/bin/env python3
"""Plan the fast Lean development compile and its target-scoped project cache."""

from __future__ import annotations

import argparse
import collections
import hashlib
import os
from pathlib import Path
import re
import tomllib


ROOT_MODULE = "GroupApproximation"
ROOT_SOURCE = Path("GroupApproximation.lean")
WORKFLOW_PATH = ".github/workflows/lean-dev-fast.yml"
HELPER_PATH = "scripts/lean_dev_plan.py"
FULL_INPUTS = {
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    WORKFLOW_PATH,
    HELPER_PATH,
    "__FULL__",
}
IMPORT_RE = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*"
    r"import(?:[ \t]+all)?[ \t]+([A-Za-z0-9_.]+)",
    re.MULTILINE,
)


def mask_lean_comments_and_strings(text: str) -> str:
    """Mask nested comments and strings while preserving newlines."""
    masked = list(text)
    depth = 0
    in_string = False
    i = 0
    while i < len(text):
        if depth == 0 and not in_string and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                masked[i] = " "
                i += 1
            continue
        if not in_string and text.startswith("/-", i):
            depth += 1
            masked[i] = masked[i + 1] = " "
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            masked[i] = masked[i + 1] = " "
            i += 2
            continue
        if depth > 0:
            if text[i] != "\n":
                masked[i] = " "
            i += 1
            continue
        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                masked[i] = " "
                if text[i + 1] != "\n":
                    masked[i + 1] = " "
                i += 2
                continue
            if text[i] == '"':
                in_string = False
            if text[i] != "\n":
                masked[i] = " "
            i += 1
            continue
        if text[i] == '"':
            in_string = True
            masked[i] = " "
        i += 1
    if depth:
        raise RuntimeError("unterminated Lean block comment while planning dev compile")
    if in_string:
        raise RuntimeError("unterminated Lean string while planning dev compile")
    return "".join(masked)


def module_for_path(path: Path) -> str | None:
    s = path.as_posix()
    if s == ROOT_SOURCE.as_posix():
        return ROOT_MODULE
    if s.startswith(f"{ROOT_MODULE}/") and s.endswith(".lean"):
        return s[:-5].replace("/", ".")
    return None


def path_for_module(module: str) -> Path:
    if module == ROOT_MODULE:
        return ROOT_SOURCE
    return Path(module.replace(".", "/") + ".lean")


def local_modules() -> dict[str, Path]:
    modules = {
        module_for_path(path): path
        for path in Path(ROOT_MODULE).rglob("*.lean")
    }
    clean = {module: path for module, path in modules.items() if module is not None}
    if ROOT_SOURCE.is_file():
        clean[ROOT_MODULE] = ROOT_SOURCE
    return clean


def imports_of(path: Path) -> tuple[str, ...]:
    source = mask_lean_comments_and_strings(
        path.read_text(encoding="utf-8", errors="strict")
    )
    return tuple(
        module
        for module in IMPORT_RE.findall(source)
        if module == ROOT_MODULE or module.startswith(f"{ROOT_MODULE}.")
    )


def normalize_manual_target(raw: str, modules: dict[str, Path]) -> Path:
    target = raw.strip()
    if not target:
        raise ValueError("empty manual target")
    if target.endswith(".lean"):
        path = Path(target)
        module = module_for_path(path)
        if module is None:
            raise ValueError(
                "manual .lean target must be GroupApproximation.lean "
                "or live under GroupApproximation/"
            )
    else:
        target = target.removeprefix("+")
        if ":" in target:
            target = target.split(":", 1)[0]
        if not re.fullmatch(r"[A-Za-z0-9_.]+", target):
            raise ValueError(f"invalid Lean module target: {raw!r}")
        module = target
        path = path_for_module(module)
    if module not in modules or not path.is_file():
        raise ValueError(f"manual Lean target does not exist: {raw!r}")
    return path


def select_targets(
    changed: list[str], manual: str, modules: dict[str, Path]
) -> list[Path]:
    if manual.strip():
        return [normalize_manual_target(manual, modules)]

    if any(path in FULL_INPUTS for path in changed) or ROOT_SOURCE.as_posix() in changed:
        return [ROOT_SOURCE]

    reverse: dict[str, set[str]] = collections.defaultdict(set)
    for owner, path in modules.items():
        for dep in imports_of(path):
            reverse[dep].add(owner)

    selected: set[str] = set()
    deleted: set[str] = set()
    for raw in changed:
        path = Path(raw)
        module = module_for_path(path)
        if module is None or module == ROOT_MODULE:
            continue
        if path.is_file():
            selected.add(module)
        else:
            deleted.add(module)

    for module in deleted:
        selected.update(reverse.get(module, ()))

    return [modules[module] for module in sorted(selected)]


def dependency_closure(
    targets: list[Path], modules: dict[str, Path]
) -> tuple[str, ...]:
    seen: set[str] = set()
    pending: list[str] = []
    for path in targets:
        pending.extend(imports_of(path))

    while pending:
        module = pending.pop()
        if module in seen:
            continue
        path = modules.get(module)
        if path is None:
            # A missing local import should be diagnosed by `lake lean`; it
            # cannot contribute a reusable cache artifact.
            continue
        seen.add(module)
        pending.extend(imports_of(path))

    # A selected file can also be an import of another selected file. Keep it
    # in the dependency cache in that case; leaf roots naturally stay absent.
    return tuple(sorted(seen))


def digest_frame(digest, data: bytes) -> None:
    digest.update(len(data).to_bytes(8, "big"))
    digest.update(data)


def cache_digests(
    dependencies: tuple[str, ...], modules: dict[str, Path]
) -> tuple[str, str]:
    dep_set = hashlib.sha256()
    dep_set.update(b"group-approx-dev-depset-v1\0")
    for module in dependencies:
        digest_frame(dep_set, module.encode())

    content = hashlib.sha256()
    content.update(b"group-approx-dev-depcontent-v1\0")
    for config in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        path = Path(config)
        digest_frame(content, config.encode())
        digest_frame(content, path.read_bytes())
    for module in dependencies:
        path = modules[module]
        digest_frame(content, module.encode())
        digest_frame(content, path.read_bytes())
    return dep_set.hexdigest(), content.hexdigest()


def cache_paths(dependencies: tuple[str, ...]) -> list[str]:
    paths: list[str] = []
    for module in dependencies:
        stem = module.replace(".", "/")
        paths.extend(
            (
                f".lake/build/lib/lean/{stem}.olean",
                f".lake/build/lib/lean/{stem}.olean.hash",
                f".lake/build/lib/lean/{stem}.trace",
            )
        )
    return paths


def library_lean_args() -> list[str]:
    """Mirror GroupApproximation lean_lib arguments for `lake lean`."""
    data = tomllib.loads(Path("lakefile.toml").read_text(encoding="utf-8"))
    for library in data.get("lean_lib", []):
        if library.get("name") == ROOT_MODULE:
            weak = [str(arg) for arg in library.get("weakLeanArgs", [])]
            more = [str(arg) for arg in library.get("moreLeanArgs", [])]
            return weak + more
    raise RuntimeError(f"lakefile.toml has no [[lean_lib]] named {ROOT_MODULE}")


def write_multiline_output(handle, name: str, lines: list[str]) -> None:
    marker = f"__{name.upper()}_{os.getpid()}__"
    handle.write(f"{name}<<{marker}\n")
    for line in lines:
        handle.write(f"{line}\n")
    handle.write(f"{marker}\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--changed-file", required=True, type=Path)
    parser.add_argument("--manual-target", default="")
    parser.add_argument("--github-output", required=True, type=Path)
    args = parser.parse_args()

    modules = local_modules()
    if ROOT_MODULE not in modules:
        raise SystemExit(f"missing {ROOT_SOURCE}")

    changed = args.changed_file.read_text(encoding="utf-8").splitlines()
    targets = select_targets(changed, args.manual_target, modules)
    deps = dependency_closure(targets, modules) if targets else ()
    dep_set, dep_content = (
        cache_digests(deps, modules) if deps else ("none", "none")
    )
    paths = cache_paths(deps)
    extra_args = library_lean_args()

    ci = Path(".ci")
    ci.mkdir(exist_ok=True)
    (ci / "fast-lean-files").write_text(
        "".join(path.as_posix() + "\n" for path in targets), encoding="utf-8"
    )
    (ci / "fast-lean-extra-args").write_text(
        "".join(arg + "\n" for arg in extra_args), encoding="utf-8"
    )
    (ci / "fast-lean-cache-paths").write_text(
        "".join(path + "\n" for path in paths), encoding="utf-8"
    )

    print(f"selected {len(targets)} Lean file(s)")
    for path in targets:
        print(f"  check {path}")
    print(f"local import cache closure: {len(deps)} module(s)")
    if extra_args:
        print("library Lean args:", " ".join(extra_args))

    with args.github_output.open("a", encoding="utf-8") as output:
        output.write(f"skip={'true' if not targets else 'false'}\n")
        output.write(f"count={len(targets)}\n")
        output.write(f"has_project_deps={'true' if deps else 'false'}\n")
        output.write(f"dep_set={dep_set}\n")
        output.write(f"dep_content={dep_content}\n")
        write_multiline_output(output, "cache_paths", paths)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
