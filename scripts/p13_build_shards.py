#!/usr/bin/env python3
"""Build and transport the expensive canonical P13 certificate in bounded shards.

The generated residual certificate has 36 blocks, each split into four large
kernel computations.  Asking Lake to build their common aggregator exposes all
144 computations to its scheduler at once.  This helper instead builds one
module target per Lake invocation and fixes Lean's worker pool at one thread.

CI divides the blocks among twelve shards.  Each bounded job owns three blocks
(twelve large part modules and their wrappers), and the workflow limits
concurrent shards explicitly.  This keeps peak memory bounded without creating
dozens of short-lived jobs or making six runners each perform 24 large kernel
replays serially.  The resulting Lake artifacts are archived with their trace
files so a later job can merge the twelve disjoint shards and finish the
ordinary project build without recompiling an expensive leaf.
"""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
from typing import Iterable, Sequence


BLOCK_WIDTH = 6
SHARD_COUNT = 12
PART_COUNT = 4
MODULE_PREFIX = "GroupApproximation.Sofic.LiteralP13HodgeResidual"
FOUNDATION_CORE_MODULE = (
    "GroupApproximation.Sofic.LiteralP13HodgeCertificateCore"
)
FOUNDATION_COMPOSITION_MODULE = (
    "GroupApproximation.Sofic.LiteralP13HodgeResidualComposition"
)
FOUNDATION_BATCHED_CHECKS_MODULE = (
    "GroupApproximation.Meta.BatchedKernelChecks"
)
FOUNDATION_MODULES = (
    FOUNDATION_CORE_MODULE,
    FOUNDATION_COMPOSITION_MODULE,
    # Every P13 block imports the batched kernel checker, so its artifacts
    # must travel with the foundation or the sealed no-build pass finds the
    # blocks stale on the restore side.
    FOUNDATION_BATCHED_CHECKS_MODULE,
)
RESIDUAL_AGGREGATOR_MODULE = (
    "GroupApproximation.Sofic.LiteralP13HodgeResidual"
)
FINAL_CERTIFICATE_MODULE = (
    "GroupApproximation.Sofic.LiteralP13HodgeCertificate"
)
FOUNDATION_ARCHIVE = "p13-foundation.tar.gz"
CACHE_KEY_FILES = (
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "scripts/p13_build_shards.py",
    ".github/workflows/p13-sharded-build.yml",
)
LOCAL_MODULE_PREFIX = "GroupApproximation"
IMPORT_RE = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*"
    r"import(?:[ \t]+all)?[ \t]+([A-Za-z0-9_.]+)",
    re.MULTILINE,
)


def repo_root() -> Path:
    root = Path(__file__).resolve().parent.parent
    if not (root / "lakefile.toml").is_file():
        raise RuntimeError(f"repository root has no lakefile.toml: {root}")
    return root


def block_names(shard: int) -> tuple[str, ...]:
    if not 0 <= shard < SHARD_COUNT:
        raise ValueError(f"shard must be in [0, {SHARD_COUNT}), got {shard}")
    return tuple(
        f"{row}{column}"
        for row in range(BLOCK_WIDTH)
        for column in range(BLOCK_WIDTH)
        if (row * BLOCK_WIDTH + column) % SHARD_COUNT == shard
    )


def modules_for_shard(shard: int) -> tuple[str, ...]:
    modules: list[str] = []
    for block in block_names(shard):
        modules.extend(
            f"{MODULE_PREFIX}{block}Part{part}"
            for part in range(PART_COUNT)
        )
        modules.append(f"{MODULE_PREFIX}{block}")
    return tuple(modules)


def source_path(root: Path, module: str) -> Path:
    return root / f"{module.replace('.', '/')}.lean"


def module_stem(module: str) -> str:
    return module.replace(".", "/")


def mask_lean_comments_and_strings(text: str) -> str:
    """Mask nested comments and strings while preserving lines and offsets."""
    masked = list(text)
    depth = 0
    in_string = False
    index = 0
    while index < len(text):
        if depth == 0 and not in_string and text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                masked[index] = " "
                index += 1
            continue
        if not in_string and text.startswith("/-", index):
            depth += 1
            masked[index] = masked[index + 1] = " "
            index += 2
            continue
        if depth > 0 and text.startswith("-/", index):
            depth -= 1
            masked[index] = masked[index + 1] = " "
            index += 2
            continue
        if depth > 0:
            if text[index] != "\n":
                masked[index] = " "
            index += 1
            continue
        if in_string:
            if text[index] == "\\" and index + 1 < len(text):
                masked[index] = " "
                if text[index + 1] != "\n":
                    masked[index + 1] = " "
                index += 2
                continue
            if text[index] == '"':
                in_string = False
            if text[index] != "\n":
                masked[index] = " "
            index += 1
            continue
        if text[index] == '"':
            in_string = True
            masked[index] = " "
        index += 1
    if depth != 0:
        raise RuntimeError("unterminated block comment while reading Lean imports")
    if in_string:
        raise RuntimeError("unterminated string while reading Lean imports")
    return "".join(masked)


def local_module_files(root: Path) -> dict[str, Path]:
    library = root / LOCAL_MODULE_PREFIX
    modules = {
        ".".join(path.relative_to(root).with_suffix("").parts): path
        for path in library.rglob("*.lean")
    }
    root_module = root / f"{LOCAL_MODULE_PREFIX}.lean"
    if root_module.is_file():
        modules[LOCAL_MODULE_PREFIX] = root_module
    return modules


def source_closure(root: Path, roots: Sequence[str]) -> tuple[Path, ...]:
    if not roots:
        raise RuntimeError("P13 cache import closure has no roots")
    modules = local_module_files(root)
    seen: set[str] = set()
    pending = list(roots)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        path = modules.get(module)
        if path is None:
            raise RuntimeError(f"missing local module in P13 cache closure: {module}")
        if path.is_symlink():
            raise RuntimeError(f"refusing symlinked P13 source: {path}")
        seen.add(module)
        source = mask_lean_comments_and_strings(
            path.read_text(encoding="utf-8", errors="strict")
        )
        for imported in IMPORT_RE.findall(source):
            if imported == LOCAL_MODULE_PREFIX or imported.startswith(
                f"{LOCAL_MODULE_PREFIX}."
            ):
                if imported not in modules:
                    raise RuntimeError(
                        f"{module} imports missing local module {imported}"
                    )
                pending.append(imported)
    return tuple(
        sorted((modules[module] for module in seen), key=lambda path: path.as_posix())
    )


def cache_key_inputs(root: Path, roots: Sequence[str]) -> tuple[Path, ...]:
    inputs = set(source_closure(root, roots))
    for relative in CACHE_KEY_FILES:
        path = root / relative
        if not path.is_file():
            raise RuntimeError(f"missing P13 cache-key input: {path}")
        if path.is_symlink():
            raise RuntimeError(f"refusing symlinked P13 cache-key input: {path}")
        inputs.add(path)
    return tuple(sorted(inputs, key=lambda p: p.relative_to(root).as_posix()))


def update_digest_frame(digest, value: bytes) -> None:
    digest.update(len(value).to_bytes(8, "big"))
    digest.update(value)


def content_cache_key(
    root: Path, *, scope: str, roots: Sequence[str]
) -> str:
    root_modules = tuple(sorted(set(roots)))
    inputs = cache_key_inputs(root, root_modules)
    digest = hashlib.sha256()
    digest.update(b"canonical-p13-build-cache-v2\0")
    digest.update(b"scope\0")
    update_digest_frame(digest, scope.encode("utf-8"))
    digest.update(b"roots\0")
    digest.update(len(root_modules).to_bytes(8, "big"))
    for module in root_modules:
        update_digest_frame(digest, module.encode("utf-8"))
    digest.update(b"inputs\0")
    digest.update(len(inputs).to_bytes(8, "big"))
    for path in inputs:
        update_digest_frame(
            digest, path.relative_to(root).as_posix().encode("utf-8")
        )
        update_digest_frame(digest, hashlib.sha256(path.read_bytes()).digest())
    return digest.hexdigest()


def foundation_cache_key(root: Path) -> str:
    return content_cache_key(
        root, scope="foundation", roots=FOUNDATION_MODULES
    )


def shard_cache_key(root: Path, shard: int) -> str:
    return content_cache_key(
        root, scope=f"shard-{shard}", roots=modules_for_shard(shard)
    )


def required_artifacts(module: str) -> tuple[str, ...]:
    stem = module_stem(module)
    return (
        f".lake/build/lib/lean/{stem}.olean",
        f".lake/build/lib/lean/{stem}.olean.hash",
        f".lake/build/lib/lean/{stem}.ilean",
        f".lake/build/lib/lean/{stem}.ilean.hash",
        f".lake/build/lib/lean/{stem}.trace",
        f".lake/build/ir/{stem}.c",
        f".lake/build/ir/{stem}.c.hash",
        f".lake/build/ir/{stem}.setup.json",
    )


def assert_sources(root: Path, modules: Iterable[str]) -> None:
    missing = [str(source_path(root, module)) for module in modules
               if not source_path(root, module).is_file()]
    if missing:
        raise RuntimeError("missing P13 source modules:\n" + "\n".join(missing))


def run_lake(root: Path, arguments: Sequence[str]) -> None:
    env = os.environ.copy()
    # Lake 5 schedules builds through Lean's task pool and has no build-command
    # jobs flag.  This runtime control bounds both Lake and the compiler child.
    env["LEAN_NUM_THREADS"] = "1"
    subprocess.run(
        ["taskset", "-c", "0", "lake", *arguments],
        cwd=root,
        env=env,
        check=True,
    )


def run_module_build(root: Path, module: str) -> None:
    run_lake(root, ("build", f"+{module}:olean"))


def artifact_files_for_modules(root: Path, modules: Sequence[str]) -> list[Path]:
    files: set[Path] = set()
    for module in modules:
        stem = module_stem(module)
        for artifact_root in (
            root / ".lake/build/lib/lean",
            root / ".lake/build/ir",
        ):
            parent = artifact_root / str(PurePosixPath(stem).parent)
            basename = PurePosixPath(stem).name
            if parent.is_dir():
                for path in parent.glob(f"{basename}.*"):
                    if path.is_symlink():
                        raise RuntimeError(f"refusing symlinked build artifact: {path}")
                    if path.is_file():
                        files.add(path)

    missing = [relative for module in modules
               for relative in required_artifacts(module)
               if not (root / relative).is_file()]
    if missing:
        raise RuntimeError(
            "Lake did not produce the required P13 artifacts:\n"
            + "\n".join(missing)
        )
    return sorted(files)


def all_foundation_files(root: Path) -> list[Path]:
    build = root / ".lake/build"
    if not build.is_dir():
        raise RuntimeError("foundation build produced no .lake/build directory")
    files: list[Path] = []
    # A foundation job deliberately starts without a project-build restore.
    # Keep only Lake's module-output trees; configuration and any future
    # top-level products do not belong in a transport artifact.
    for artifact_root in (build / "lib", build / "ir"):
        if not artifact_root.is_dir():
            continue
        for path in artifact_root.rglob("*"):
            if path.is_symlink():
                raise RuntimeError(f"refusing symlinked build artifact: {path}")
            if path.is_file():
                files.append(path)
    missing = [relative for module in FOUNDATION_MODULES
               for relative in required_artifacts(module)
               if not (root / relative).is_file()]
    if missing:
        raise RuntimeError(
            "Lake did not produce the required P13 foundation artifacts:\n"
            + "\n".join(missing)
        )
    return sorted(files)


def write_archive(root: Path, archive: Path, files: Sequence[Path]) -> None:
    if not files:
        raise RuntimeError("refusing to create an empty P13 artifact archive")
    archive.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, mode="w:gz", compresslevel=6) as output:
        for path in files:
            output.add(path, arcname=path.relative_to(root).as_posix(), recursive=False)
    print(f"wrote {archive} with {len(files)} files")


def build_foundation(root: Path, archive: Path) -> None:
    assert_sources(root, FOUNDATION_MODULES)
    for module in FOUNDATION_MODULES:
        run_module_build(root, module)
    write_archive(root, archive, all_foundation_files(root))


def build_shard(root: Path, shard: int, archive: Path) -> None:
    modules = modules_for_shard(shard)
    assert_sources(root, modules)
    for module in modules:
        run_module_build(root, module)
    write_archive(root, archive, artifact_files_for_modules(root, modules))


def normalized_member_name(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise RuntimeError(f"unsafe path in P13 artifact archive: {name!r}")
    if path.as_posix() != name:
        raise RuntimeError(f"non-normalized path in P13 artifact archive: {name!r}")
    if path.parts[:3] != (".lake", "build", "lib") and path.parts[:3] != (
        ".lake", "build", "ir"
    ):
        raise RuntimeError(f"unexpected path in P13 artifact archive: {name!r}")
    return path


def validate_archive(
    archive: Path, *, allowed_modules: Sequence[str] | None
) -> tuple[tarfile.TarInfo, ...]:
    if not archive.is_file():
        raise RuntimeError(f"missing P13 artifact archive: {archive}")
    allowed_stems = None if allowed_modules is None else tuple(
        module_stem(module) for module in allowed_modules
    )
    seen: set[str] = set()
    with tarfile.open(archive, mode="r:gz") as source:
        members = tuple(source.getmembers())
    if not members:
        raise RuntimeError(f"empty P13 artifact archive: {archive}")
    for member in members:
        path = normalized_member_name(member.name)
        if not member.isfile():
            raise RuntimeError(
                f"non-regular member in P13 artifact archive: {member.name!r}"
            )
        if member.name in seen:
            raise RuntimeError(
                f"duplicate member in P13 artifact archive: {member.name!r}"
            )
        seen.add(member.name)
        if allowed_stems is not None:
            if path.parts[:5] == (".lake", "build", "lib", "lean", "GroupApproximation"):
                relative = "/".join(path.parts[4:])
            elif path.parts[:4] == (".lake", "build", "ir", "GroupApproximation"):
                relative = "/".join(path.parts[3:])
            else:
                raise RuntimeError(
                    f"non-module path in P13 shard archive: {member.name!r}"
                )
            if not any(relative.startswith(f"{stem}.") for stem in allowed_stems):
                raise RuntimeError(
                    f"artifact does not belong to this P13 shard: {member.name!r}"
                )
    if allowed_modules is not None:
        missing = [relative for module in allowed_modules
                   for relative in required_artifacts(module)
                   if relative not in seen]
        if missing:
            raise RuntimeError(
                f"incomplete P13 shard archive {archive}:\n" + "\n".join(missing)
            )
    return members


def extract_archive(
    root: Path, archive: Path, *, allowed_modules: Sequence[str] | None
) -> set[str]:
    members = validate_archive(archive, allowed_modules=allowed_modules)
    with tarfile.open(archive, mode="r:gz") as source:
        source.extractall(root, members=members, filter="data")
    return {member.name for member in members}


def restore_foundation(root: Path, archive: Path) -> None:
    restored = extract_archive(root, archive, allowed_modules=None)
    missing = [relative for module in FOUNDATION_MODULES
               for relative in required_artifacts(module)
               if relative not in restored]
    if missing:
        raise RuntimeError(
            f"incomplete P13 foundation archive {archive}:\n"
            + "\n".join(missing)
        )
    print(f"restored P13 foundation from {archive}")


def find_one(directory: Path, name: str) -> Path:
    matches = sorted(directory.rglob(name))
    if len(matches) != 1:
        raise RuntimeError(
            f"expected exactly one {name} below {directory}, found {len(matches)}"
        )
    return matches[0]


def restore_all(root: Path, directory: Path) -> None:
    archives: list[tuple[Path, Sequence[str] | None]] = [
        (find_one(directory, FOUNDATION_ARCHIVE), None)
    ]
    archives.extend(
        (find_one(directory, f"p13-shard-{shard}.tar.gz"),
         modules_for_shard(shard))
        for shard in range(SHARD_COUNT)
    )

    member_sets: list[set[str]] = []
    for archive, modules in archives:
        members = validate_archive(archive, allowed_modules=modules)
        names = {member.name for member in members}
        overlap = set().union(*member_sets).intersection(names) if member_sets else set()
        if overlap:
            raise RuntimeError(
                "P13 artifact archives overlap:\n" + "\n".join(sorted(overlap))
            )
        member_sets.append(names)

    for archive, modules in archives:
        extract_archive(root, archive, allowed_modules=modules)

    expected_modules = tuple(
        module
        for shard in range(SHARD_COUNT)
        for module in modules_for_shard(shard)
    )
    missing = [relative for module in expected_modules
               for relative in required_artifacts(module)
               if not (root / relative).is_file()]
    if missing:
        raise RuntimeError(
            "merged P13 artifacts are incomplete:\n" + "\n".join(missing)
        )
    print(
        f"restored the foundation and {SHARD_COUNT} P13 shards "
        f"({len(expected_modules)} modules)"
    )


def seal_restored_shards(root: Path) -> None:
    """Replay every restored trace under the bounded scheduler.

    The no-build pass rejects a missing or stale block (and therefore a missing
    or stale part) without compiling anything.  Only after that succeeds may
    the tiny common aggregator itself be built.
    """
    assert_sources(root, (RESIDUAL_AGGREGATOR_MODULE, FINAL_CERTIFICATE_MODULE))
    blocks = tuple(
        f"{MODULE_PREFIX}{row}{column}"
        for row in range(BLOCK_WIDTH)
        for column in range(BLOCK_WIDTH)
    )
    run_lake(
        root,
        ("build", "--no-build", *(f"+{module}:olean" for module in blocks)),
    )
    restored_modules = tuple(
        module
        for shard in range(SHARD_COUNT)
        for module in modules_for_shard(shard)
    )

    def snapshot() -> dict[str, tuple[int, int]]:
        result: dict[str, tuple[int, int]] = {}
        for module in restored_modules:
            for relative in required_artifacts(module):
                stat = (root / relative).stat()
                result[relative] = (stat.st_size, stat.st_mtime_ns)
        return result

    before = snapshot()
    run_module_build(root, RESIDUAL_AGGREGATOR_MODULE)
    run_module_build(root, FINAL_CERTIFICATE_MODULE)
    after = snapshot()
    if before != after:
        changed = sorted(
            relative for relative in before.keys() | after.keys()
            if before.get(relative) != after.get(relative)
        )
        raise RuntimeError(
            "sealing unexpectedly changed a restored P13 leaf/block artifact:\n"
            + "\n".join(changed)
        )
    print(
        f"sealed {len(restored_modules)} restored P13 modules and the final "
        "certificate without rebuilding a leaf or block"
    )


def self_test(root: Path) -> None:
    blocks = [block for shard in range(SHARD_COUNT) for block in block_names(shard)]
    expected_blocks = [f"{row}{column}" for row in range(BLOCK_WIDTH)
                       for column in range(BLOCK_WIDTH)]
    if sorted(blocks) != expected_blocks or len(set(blocks)) != BLOCK_WIDTH**2:
        raise RuntimeError("P13 shard partition is not exhaustive and disjoint")
    modules = [module for shard in range(SHARD_COUNT)
               for module in modules_for_shard(shard)]
    if len(modules) != BLOCK_WIDTH**2 * (PART_COUNT + 1):
        raise RuntimeError("P13 shard module roster has the wrong size")
    if len(set(modules)) != len(modules):
        raise RuntimeError("P13 shard module roster contains duplicates")
    assert_sources(root, (*FOUNDATION_MODULES, *modules))

    def closure_modules(roots: Sequence[str]) -> set[str]:
        return {
            path.relative_to(root).with_suffix("").as_posix().replace("/", ".")
            for path in source_closure(root, roots)
        }

    wrappers = {RESIDUAL_AGGREGATOR_MODULE, FINAL_CERTIFICATE_MODULE}
    generated_modules = set(modules)
    foundation_closure = closure_modules(FOUNDATION_MODULES)
    unexpected_foundation = sorted(
        foundation_closure.intersection(generated_modules | wrappers)
    )
    missing_foundation = sorted(set(FOUNDATION_MODULES) - foundation_closure)
    if missing_foundation or unexpected_foundation:
        raise RuntimeError(
            "P13 foundation cache closure crosses a generated-module boundary:\n"
            + "\n".join(missing_foundation + unexpected_foundation)
        )

    keys = [("foundation", foundation_cache_key(root))]
    shard_closure_sizes: list[int] = []
    for shard in range(SHARD_COUNT):
        roots = set(modules_for_shard(shard))
        closure = closure_modules(tuple(roots))
        missing = sorted((roots | foundation_closure) - closure)
        if missing:
            raise RuntimeError(
                f"P13 shard {shard} cache closure misses required modules:\n"
                + "\n".join(missing)
            )
        foreign = sorted(closure.intersection(generated_modules - roots))
        unexpected_wrappers = sorted(closure.intersection(wrappers))
        if foreign or unexpected_wrappers:
            raise RuntimeError(
                f"P13 shard {shard} cache closure crosses a shard boundary:\n"
                + "\n".join(foreign + unexpected_wrappers)
            )
        shard_closure_sizes.append(len(closure))
        keys.append((f"shard {shard}", shard_cache_key(root, shard)))

    for label, key in keys:
        if not re.fullmatch(r"[0-9a-f]{64}", key):
            raise RuntimeError(f"invalid P13 {label} content cache key: {key!r}")
    if len({key for _, key in keys}) != len(keys):
        raise RuntimeError("P13 cache scopes produced duplicate content keys")
    print(
        f"P13 shard roster: {BLOCK_WIDTH**2 * PART_COUNT} part modules and "
        f"{BLOCK_WIDTH**2} block modules across {SHARD_COUNT} disjoint shards; "
        f"cache closures: {len(foundation_closure)} foundation modules and "
        f"{min(shard_closure_sizes)}--{max(shard_closure_sizes)} modules per shard"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    foundation = subparsers.add_parser("build-foundation")
    foundation.add_argument("--archive", type=Path, required=True)

    shard = subparsers.add_parser("build-shard")
    shard.add_argument("--shard", type=int, required=True)
    shard.add_argument("--archive", type=Path, required=True)

    restore = subparsers.add_parser("restore-foundation")
    restore.add_argument("--archive", type=Path, required=True)

    restore_everything = subparsers.add_parser("restore-all")
    restore_everything.add_argument("--directory", type=Path, required=True)

    cache_key = subparsers.add_parser("cache-key")
    cache_scopes = cache_key.add_subparsers(dest="cache_scope", required=True)
    cache_scopes.add_parser("foundation")
    cache_shard = cache_scopes.add_parser("shard")
    cache_shard.add_argument("--shard", type=int, required=True)
    subparsers.add_parser("seal")
    subparsers.add_parser("self-test")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = repo_root()
    if args.command == "build-foundation":
        build_foundation(root, args.archive.resolve())
    elif args.command == "build-shard":
        build_shard(root, args.shard, args.archive.resolve())
    elif args.command == "restore-foundation":
        restore_foundation(root, args.archive.resolve())
    elif args.command == "restore-all":
        restore_all(root, args.directory.resolve())
    elif args.command == "cache-key":
        if args.cache_scope == "foundation":
            print(foundation_cache_key(root))
        elif args.cache_scope == "shard":
            print(shard_cache_key(root, args.shard))
        else:
            raise AssertionError(f"unhandled cache scope: {args.cache_scope}")
    elif args.command == "seal":
        seal_restored_shards(root)
    elif args.command == "self-test":
        self_test(root)
    else:
        raise AssertionError(f"unhandled command: {args.command}")


if __name__ == "__main__":
    main()
