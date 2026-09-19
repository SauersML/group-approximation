#!/usr/bin/env python3
"""Is the first stubborn core a union of small gadgets, or one atom?

For S(1,2) = S_(2,4) = X_1 X_2 the first stubborn layer is a = 4 and the core has 24 points.
This script checks, exhaustively:

 1. no subset of the core of size <= 4 is stubborn (so no bounded gadget generates it);
 2. no proper subset obtained by deleting one point is stubborn (so the core is a MINIMAL
    stubborn set, not merely the maximal one);
 3. the six root-leaf-profile classes of the core (4 points each) are individually non-stubborn,
    and it reports how many private successors each point of a class then has;
 4. the core is invariant under the mirror involution (reverse the root order, mirror every tree),
    which is a symmetry of S(1,2) as a set of forests -- and so is the 1092-point S(2,2) core.

Run:  python3 core_atoms.py
"""
import collections
import itertools
import json

from forests import K_of, graft, mono_forest, n_leaves, peel, stubborn_core


def show(t):
    return "." if t == 0 else "(" + show(t[0]) + show(t[1]) + ")"


def showf(u):
    return " ".join(show(t) for t in u)


def mirror_tree(t):
    return 0 if t == 0 else (mirror_tree(t[1]), mirror_tree(t[0]))


def mirror(u):
    return tuple(mirror_tree(t) for t in reversed(u))


def private_counts(S, Z):
    """for each z in Z, the number of w in S z with N(w) cap Z = {z}"""
    K = K_of(S)
    SF = [mono_forest(s, K) for s in S]
    Zs = set(Z)
    out = {}
    for u in Z:
        c = 0
        for sf in SF:
            w = graft(sf, u)
            hits = [p for p in (peel(sf2, w) for sf2 in SF) if p is not None and p in Zs]
            if hits == [u]:
                c += 1
        out[u] = c
    return out


def is_stubborn(S, Z):
    return all(c <= 1 for c in private_counts(S, Z).values())


S12 = [(i, j) for i in range(2) for j in range(i, 3)]
S22 = [(i, j) for i in range(3) for j in range(i, 4)]

_, core = stubborn_core(S12, 4)
rep = {"set": "S(1,2)=S_(2,4)", "a": 4, "core": len(core)}

# 1 -- small subsets
rep["stubborn_subsets_of_size_at_most_4"] = sum(
    1 for k in (1, 2, 3, 4) for Z in itertools.combinations(core, k) if is_stubborn(S12, Z))

# 2 -- one-point deletions
rep["stubborn_subsets_missing_one_point"] = sum(
    1 for i in range(len(core)) if is_stubborn(S12, core[:i] + core[i + 1:]))

# 3 -- profile classes
byprof = collections.defaultdict(list)
for u in core:
    byprof[tuple(n_leaves(t) for t in u)].append(u)
rep["profile_classes"] = {str(p): len(v) for p, v in sorted(byprof.items())}
rep["profile_class_private_counts"] = {
    str(p): sorted(private_counts(S12, v).values()) for p, v in sorted(byprof.items())}

# 4 -- mirror symmetry
SF12 = set(mono_forest(s, K_of(S12)) for s in S12)
rep["S(1,2)_is_mirror_symmetric"] = set(mirror(f) for f in SF12) == SF12
rep["core_is_mirror_symmetric"] = set(mirror(u) for u in core) == set(core)

SF22 = set(mono_forest(s, K_of(S22)) for s in S22)
_, core22 = stubborn_core(S22, 7)
rep["S(2,2)_is_mirror_symmetric"] = set(mirror(f) for f in SF22) == SF22
rep["S(2,2)_core_is_mirror_symmetric"] = set(mirror(u) for u in core22) == set(core22)
rep["S(2,2)_core"] = len(core22)

print(json.dumps(rep, indent=1))
