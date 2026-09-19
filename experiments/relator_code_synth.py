#!/usr/bin/env python3
"""Exact finite backend for compiler-guided relator-code synthesis.

Input JSON has `profiles`, `relators`, a `covers` map relator -> profiles, and
`forbidden` relator supports. A selected relator set must hit every profile and
must not contain any complete forbidden support. The latter can encode finite
collapse certificates for a protected short ball. The solver minimizes the
number of selected relators and emits a certificate independently checkable
with `--check`.

This script intentionally knows no operator algebra. The mathematical front end
must produce the finite profile cover relation and sound collapse certificates;
this file is the SAT/hitting-set backend only.
"""

import argparse
import json
import sys


def normalize(data):
    profiles = tuple(dict.fromkeys(data.get("profiles", [])))
    relators = tuple(dict.fromkeys(data.get("relators", [])))
    if not all(isinstance(x, str) for x in profiles + relators):
        raise ValueError("profiles and relators must be arrays of strings")
    pset, rset = set(profiles), set(relators)
    covers_raw = data.get("covers", {})
    if not isinstance(covers_raw, dict):
        raise ValueError("covers must be an object relator -> profile list")
    covers = {r: frozenset(covers_raw.get(r, [])) for r in relators}
    for r, ps in covers.items():
        unknown = set(ps) - pset
        if unknown:
            raise ValueError(f"covers[{r!r}] contains unknown profiles: {sorted(unknown)}")
    extra = set(covers_raw) - rset
    if extra:
        raise ValueError(f"covers has unknown relators: {sorted(extra)}")
    forbidden = []
    for i, row in enumerate(data.get("forbidden", [])):
        if not isinstance(row, list) or not row:
            raise ValueError(f"forbidden[{i}] must be a nonempty relator list")
        c = frozenset(row)
        unknown = c - rset
        if unknown:
            raise ValueError(f"forbidden[{i}] has unknown relators: {sorted(unknown)}")
        forbidden.append(c)
    by_profile = {p: tuple(r for r in relators if p in covers[r]) for p in profiles}
    impossible = [p for p, rs in by_profile.items() if not rs]
    if impossible:
        raise ValueError(f"profiles with no covering relator: {impossible}")
    return profiles, relators, covers, tuple(forbidden), by_profile


def verify(instance, selected):
    profiles, relators, covers, forbidden, _ = instance
    chosen = frozenset(selected)
    unknown = chosen - set(relators)
    uncovered = [p for p in profiles if not any(p in covers[r] for r in chosen)]
    violated = [sorted(c) for c in forbidden if c <= chosen]
    return {
        "valid": not unknown and not uncovered and not violated,
        "unknown_relators": sorted(unknown),
        "uncovered_profiles": uncovered,
        "violated_forbidden_supports": violated,
    }


def solve(instance):
    profiles, _, covers, forbidden, by_profile = instance
    best = None
    nodes = 0

    def rec(chosen):
        nonlocal best, nodes
        nodes += 1
        chosen = frozenset(chosen)
        if best is not None and len(chosen) >= len(best):
            return
        if any(c <= chosen for c in forbidden):
            return
        uncovered = [p for p in profiles
                     if not any(p in covers[r] for r in chosen)]
        if not uncovered:
            best = chosen
            return
        p = min(uncovered, key=lambda q: sum(
            1 for r in by_profile[q] if r not in chosen))
        options = [r for r in by_profile[p] if r not in chosen]
        options.sort(key=lambda r: (-sum(1 for q in uncovered if q in covers[r]), r))
        for r in options:
            rec(chosen | {r})

    rec(frozenset())
    return best, nodes


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("instance", help="JSON synthesis instance")
    ap.add_argument("--check", metavar="CERTIFICATE",
                    help="verify a JSON certificate instead of solving")
    args = ap.parse_args(argv)
    try:
        with open(args.instance, encoding="utf-8") as f:
            instance = normalize(json.load(f))
        if args.check:
            with open(args.check, encoding="utf-8") as f:
                cert = json.load(f)
            selected = cert.get("selected", [])
            result = {"status": "ok", "selected": selected,
                      "verification": verify(instance, selected)}
            print(json.dumps(result, indent=2, sort_keys=True))
            return 0 if result["verification"]["valid"] else 2
        selected, nodes = solve(instance)
        if selected is None:
            print(json.dumps({"status": "unsat", "search_nodes": nodes},
                             indent=2, sort_keys=True))
            return 1
        selected = sorted(selected)
        out = {
            "status": "sat",
            "objective": len(selected),
            "selected": selected,
            "search_nodes": nodes,
            "verification": verify(instance, selected),
        }
        print(json.dumps(out, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 64


if __name__ == "__main__":
    raise SystemExit(main())
