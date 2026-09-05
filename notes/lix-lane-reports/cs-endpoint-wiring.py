#!/usr/bin/env python3
"""Root-wiring proposal for lane cs-endpoint.

Reads the actual `import GroupApproximation.…` lines of every module under
GroupApproximation/, computes the transitive closure of the cs-endpoint
endpoint modules, checks the whole project graph for cycles, and prints a
topologically ordered list of the modules the root does not yet import.
"""
import os, re, sys
from collections import defaultdict

ROOT = "/Users/user/nonsofic_existence"
PKG = "GroupApproximation"
IMP = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")

def mod_of(path):
    rel = os.path.relpath(path, ROOT)
    return rel[:-5].replace(os.sep, ".")

edges = {}          # module -> list of project modules it imports
files = {}
for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, PKG)):
    for fn in filenames:
        if not fn.endswith(".lean"):
            continue
        p = os.path.join(dirpath, fn)
        m = mod_of(p)
        files[m] = p
        deps = []
        with open(p, encoding="utf-8") as f:
            for line in f:
                g = IMP.match(line)
                if g:
                    d = g.group(1)
                    if d.split(".")[0] == PKG:
                        deps.append(d)
                elif line.strip() and not line.startswith("--"):
                    break
        edges[m] = deps

# root imports
root_imports = []
with open(os.path.join(ROOT, PKG + ".lean"), encoding="utf-8") as f:
    for line in f:
        g = IMP.match(line)
        if g and g.group(1).split(".")[0] == PKG:
            root_imports.append(g.group(1))
root_set = set(root_imports)

# dangling
dangling = sorted({d for m in edges for d in edges[m] if d not in files})
if dangling:
    print("DANGLING project imports (module has no source file):")
    for d in dangling:
        who = sorted(m for m in edges if d in edges[m])
        print(f"  {d}   imported by {', '.join(who)}")
    print()

# cycle check over the whole project graph (transitive, not just neighbours)
WHITE, GREY, BLACK = 0, 1, 2
color = defaultdict(int)
stack = []
cycles = []
def dfs(u):
    color[u] = GREY
    stack.append(u)
    for v in edges.get(u, []):
        if v not in files:
            continue
        if color[v] == GREY:
            i = stack.index(v)
            cycles.append(stack[i:] + [v])
        elif color[v] == WHITE:
            dfs(v)
    stack.pop()
    color[u] = BLACK
sys.setrecursionlimit(100000)
for m in sorted(files):
    if color[m] == WHITE:
        dfs(m)
print(f"cycles in the whole GroupApproximation/ graph: {len(cycles)}")
for c in cycles:
    print("   " + " -> ".join(c))
print()

# transitive closure of the endpoint targets, in topological order
targets = sys.argv[1:] or [
    f"{PKG}.Manuscript.NinetyNineProblems.ProblemLIX",
]
targets = [t for t in targets if t in files]
seen, order = set(), []
def topo(u):
    if u in seen or u not in files:
        return
    seen.add(u)
    for v in edges.get(u, []):
        topo(v)
    order.append(u)
for t in targets:
    topo(t)

new = [m for m in order if m not in root_set]
print(f"closure of {targets}: {len(order)} modules, {len(new)} not yet imported by the root")
print("ordered list to append to GroupApproximation.lean (dependencies first):")
for m in new:
    print(f"import {m}")
