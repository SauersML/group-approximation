#!/usr/bin/env python3
"""Wire orphan GroupApproximation modules into the root import file.

Lanes are forbidden from editing `GroupApproximation.lean`: a lane that edits
the root in a shared working tree races every other lane, and a root import
that lands without its module -- or with a module whose own imports dangle --
takes main red for everyone.  So the lead wires, with this script, which
refuses to wire anything it cannot prove is safe.

    scripts/wire_orphans.py                 report only (default)
    scripts/wire_orphans.py --wire M1 M2    wire the named modules
    scripts/wire_orphans.py --wire-all-safe wire every orphan that passes

Three refusals, each of which has taken this repository's main branch red
before:

* a **dangling** transitive import (a module importing a name with no file)
  breaks every importer, and the breakage is invisible until something in the
  root closure reaches it;
* an import **cycle** is invisible to build probes, which happily replay
  oleans, so it must be caught here;
* a lexical `sorry`/`admit`/`axiom` anywhere in the new module's own transitive
  orphan closure would put an unproved step into the advertised library.

Only `GroupApproximation.*` imports participate; Mathlib and third-party
imports are resolved as leaves.

**"Safe" here is lexical, not semantic.**  This script cannot tell whether a
module compiles -- it can only tell that wiring it will not break the root for
a reason that is visible in the source.  A module must therefore have a GREEN
remote probe of its own before it is wired, and the probe must be a real
rebuild (an unchanged `Build completed successfully (N jobs)` count means the
olean was replayed, not rebuilt).  Wiring an uncompiled module is how a lane's
work takes main red for nineteen other lanes.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ROOT_MODULE = ROOT / "GroupApproximation.lean"
SRC = ROOT / "GroupApproximation"
IMPORT_RE = re.compile(r"^import\s+(GroupApproximation(?:\.[A-Za-z0-9_']+)*)\s*$")
# A comment-aware scan: these tokens matter only outside `--` and `/- -/`.
BAD_TOKEN_RE = re.compile(r"\b(sorry|admit)\b|^\s*axiom\s")

def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def path_of(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def strip_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def load_graph() -> tuple[dict[str, list[str]], dict[str, str]]:
    """module -> its GroupApproximation imports, and module -> source text."""
    graph: dict[str, list[str]] = {}
    text: dict[str, str] = {}
    files = [ROOT_MODULE] + sorted(SRC.rglob("*.lean"))
    for f in files:
        m = module_of(f)
        body = f.read_text(encoding="utf-8", errors="replace")
        text[m] = body
        graph[m] = [
            g.group(1)
            for line in body.splitlines()
            if (g := IMPORT_RE.match(line.strip()))
        ]
    return graph, text


def reachable(graph: dict[str, list[str]], start: str) -> set[str]:
    seen, stack = set(), [start]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(graph.get(m, ()))
    return seen


def find_cycles(graph: dict[str, list[str]]) -> list[list[str]]:
    WHITE, GREY, BLACK = 0, 1, 2
    colour: dict[str, int] = {}
    cycles: list[list[str]] = []

    def walk(m: str, path: list[str]) -> None:
        colour[m] = GREY
        path.append(m)
        for n in graph.get(m, ()):
            if n not in graph:
                continue
            c = colour.get(n, WHITE)
            if c == GREY:
                cycles.append(path[path.index(n):] + [n])
            elif c == WHITE:
                walk(n, path)
        path.pop()
        colour[m] = BLACK

    sys.setrecursionlimit(20000)
    for m in graph:
        if colour.get(m, WHITE) == WHITE:
            walk(m, [])
    return cycles


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--wire", nargs="*", metavar="MODULE")
    ap.add_argument("--wire-all-safe", action="store_true")
    args = ap.parse_args()

    graph, text = load_graph()
    known = set(graph)

    dangling: dict[str, list[str]] = {}
    for m, deps in graph.items():
        missing = [d for d in deps if d not in known]
        if missing:
            dangling[m] = missing

    cycles = find_cycles(graph)
    closure = reachable(graph, "GroupApproximation")
    orphans = sorted(known - closure - {"GroupApproximation"})

    def unsafe(m: str) -> str | None:
        """Why `m` must not be wired, or None."""
        deps = reachable(graph, m)
        for d in sorted(deps):
            if d not in known:
                return f"dangling import {d}"
            for miss in dangling.get(d, ()):
                return f"transitive dangling import {miss} (via {d})"
            if BAD_TOKEN_RE.search(strip_comments(text[d])):
                return f"sorry/admit/axiom in {d}"
        for cyc in cycles:
            if deps & set(cyc):
                return f"import cycle {' -> '.join(cyc)}"
        return None

    print(f"modules: {len(known)}   root closure: {len(closure)}   orphans: {len(orphans)}")
    if dangling:
        print(f"\nDANGLING IMPORTS ({len(dangling)} modules) -- these break every importer:")
        for m, miss in sorted(dangling.items()):
            print(f"  {m}: {', '.join(miss)}")
    if cycles:
        print(f"\nIMPORT CYCLES ({len(cycles)}) -- invisible to build probes:")
        for cyc in cycles[:20]:
            print("  " + " -> ".join(cyc))

    verdicts = {m: unsafe(m) for m in orphans}
    safe = [m for m, why in verdicts.items() if why is None]
    print(f"\norphans safe to wire: {len(safe)} of {len(orphans)}")
    for m in orphans:
        why = verdicts[m]
        print(f"  {'OK  ' if why is None else 'HOLD'} {m}" + (f"  [{why}]" if why else ""))

    chosen: list[str] = []
    if args.wire_all_safe:
        chosen = safe
    elif args.wire:
        for m in args.wire:
            if verdicts.get(m) is not None:
                print(f"\nrefusing to wire {m}: {verdicts[m]}", file=sys.stderr)
                return 1
            if m not in orphans:
                print(f"\n{m} is already in the root closure; nothing to do")
            else:
                chosen.append(m)
    if not chosen:
        return 0

    # Lean 4 requires every `import` to precede EVERY other command, the module
    # docstring included.  Appending to the end of the root file produces a
    # syntax error that stops the whole library parsing -- and the visible
    # symptom is not a Lean error but a garbage orphan count, because
    # `scripts/check.py` can no longer read the root.  (Landed and caught
    # 2026-09-05: the count jumped 281 -> 2744.)  So INSERT after the last
    # existing import rather than appending.
    src = ROOT_MODULE.read_text(encoding="utf-8").splitlines(keepends=True)
    already = {ln.strip() for ln in src if ln.startswith("import ")}
    add = [f"import {m}\n" for m in chosen if f"import {m}" not in already]
    if not add:
        print("\nall chosen modules are already imported by the root")
        return 0
    last_import = max(i for i, ln in enumerate(src) if ln.startswith("import "))
    out = src[: last_import + 1] + add + src[last_import + 1 :]
    ROOT_MODULE.write_text("".join(out), encoding="utf-8")
    print(f"\nwired {len(chosen)} module(s) into GroupApproximation.lean")
    for m in chosen:
        print(f"  + {m}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
