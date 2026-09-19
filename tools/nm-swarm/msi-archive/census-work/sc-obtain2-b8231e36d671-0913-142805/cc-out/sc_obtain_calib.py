#!/usr/bin/env python3
"""sc_obtain_calib.py <old.py> <new.py> <root>      (lane systolic-counts; runs ON MSI)

fixture: plant the candidate's PRODUCER_FIXTURE and classify each expected consumer with
         the old script and with the new one, so the new fixture shows red before, green after.
delta:   build_corpus(<root>) with both scripts; print the names only one of them discharges,
         and every declaration whose in-place heads grow under the new script.
"""
import importlib.util
import sys
import tempfile
from pathlib import Path


def load(path: str, name: str):
    sys.path.insert(0, str(Path(path).resolve().parent))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def fixture(label, target, new) -> None:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        source = root / "GroupApproximation" / "Fake" / "Resolution.lean"
        source.parent.mkdir(parents=True)
        source.write_text(new.PRODUCER_FIXTURE, encoding="utf-8")
        corpus = target.build_corpus(root)
        bad = 0
        for name, want in new.PRODUCER_FIXTURE_EXPECTED.items():
            got = sorted({detector for detector, _detail in target.classify(
                corpus, corpus.by_name[name], set(), name)})
            ok = (not got) if want is None else (want in got)
            bad += not ok
            print(f"{label} {'ok ' if ok else 'BAD'} {name:24s} want={want or 'clean'} "
                  f"got={','.join(got) or 'clean'}")
        print(f"{label} FIXTURE_BAD={bad}")


def ident(declaration) -> str:
    for field in ("name", "full_name", "declaration"):
        value = getattr(declaration, field, None)
        if isinstance(value, str):
            return value
    return repr(declaration)[:160]


def where(declaration) -> str:
    path = getattr(declaration, "path", "")
    line = getattr(declaration, "line", "")
    return f"{path}:{line}"


def main() -> int:
    old = load(sys.argv[1], "cnmu_old")
    new = load(sys.argv[2], "cnmu_new")
    root = Path(sys.argv[3])
    fixture("old", old, new)
    fixture("new", new, new)
    before = old.build_corpus(root)
    after = new.build_corpus(root)
    print(f"SIZES old-D={len(before.discharged)} new-D={len(after.discharged)}")
    for name in sorted(after.discharged - before.discharged):
        print("GAINED", name)
    for name in sorted(before.discharged - after.discharged):
        print("LOST", name)
    # Corpus.declarations is dict[Path, dict[str, Declaration]].
    declarations = [declaration for per_path in after.declarations.values()
                    for declaration in per_path.values()]
    grown = 0
    for declaration in declarations:
        extra = new.in_place_heads(declaration) - old.in_place_heads(declaration)
        if extra:
            grown += 1
            print("HEADS", ident(declaration), sorted(extra), where(declaration))
    print(f"HEADS-DECLS={grown}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
