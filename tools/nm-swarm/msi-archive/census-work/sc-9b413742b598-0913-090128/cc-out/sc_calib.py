#!/usr/bin/env python3
"""sc_calib.py <script.py> fixture | delta <root>      (lane systolic-counts; runs ON MSI)

fixture: plant PRODUCER_FIXTURE (taken from the candidate script at $NEW) in a temp
         corpus, classify every expected consumer with <script.py>, print verdicts.
delta:   build_corpus(<root>) with <script.py>; print the discharged names (D) and the
         honestly discharged names (H), one per line, sorted.
"""
import importlib.util
import os
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


def main() -> int:
    target = load(sys.argv[1], "cnmu_target")
    mode = sys.argv[2]
    if mode == "fixture":
        new = load(os.environ["NEW"], "cnmu_candidate")
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
                print(f"{'ok ' if ok else 'BAD'} {name:24s} want={want or 'clean'} "
                      f"got={','.join(got) or 'clean'}")
            print(f"FIXTURE_BAD={bad}")
        return 0
    if mode == "delta":
        corpus = target.build_corpus(Path(sys.argv[3]))
        for name in sorted(corpus.discharged):
            print("D", name)
        for name in sorted(corpus.discharged_honestly):
            print("H", name)
        return 0
    print(f"unknown mode {mode}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
