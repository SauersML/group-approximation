#!/usr/bin/env python3
"""Check the defining property of Thumann's spine for the rank-3 edge-split operad: every nontrivial split tree X
has a GREATEST spine element below it (in >=_E).  If a pair of spine elements had a minimal common upper bound M
outside the computed spine (for instance one with more than 12 pieces, beyond the exact search), X = M would fail.
Spine: spineG.py at N = 12 (closed: round 4 adds nothing, no pair truncated).
Test sets: all split trees with at most 7 pieces; random split trees with 8..80 pieces; reversing upper bounds of
random pairs (up to 400 pieces).  Calibration: the atoms alone are NOT a spine (E_01 and E_02 are both below a
flop element and have no greatest element below them together), so the check must fail on flop elements when
the spine is truncated to the atoms."""
import sys, json, time, random, itertools, runpy
sys.setrecursionlimit(200000)
T0 = time.time()
TL = float(sys.argv[1]) if len(sys.argv) > 1 else 420.0
sys.argv = ["spineG.py", "60", "12"]
G = runpy.run_path("spineG.py")
from ore import DELTA, splits, geq, tri, up
import revlib as R

PERMS = list(itertools.permutations(range(3)))
reps = list(G["spine"].values())
imgs = set()
for S in reps:
    for p in PERMS:
        imgs.add(frozenset(tri(*[tuple(v[p[k]] for k in range(3)) for v in t]) for t in S))
imgs = sorted(imgs, key=len)
atoms = [S for S in imgs if len(S) == 2]
out = {"spine_classes": len(reps), "spine_elements": len(imgs), "sizes": sorted(len(S) for S in imgs)}


def greatest(X, spine):
    below = [S for S in spine if len(S) <= len(X) and (S == X or geq(X, S))]
    if not below:
        return "none", 0
    for Gm in sorted(below, key=len, reverse=True):
        if all(S == Gm or geq(Gm, S) for S in below):
            return "ok", len(below)
    return "FAIL", len(below)


# calibration: atoms only must fail on a flop element
flop = [S for S in imgs if len(S) == 5][0]
out["calibration_atoms_only_on_flop"] = greatest(flop, atoms)[0]
out["calibration_full_spine_on_flop"] = greatest(flop, imgs)[0]
print(json.dumps(out), flush=True)

st = {"exhaustive_le7": {}, "random": {}, "reversing": {}}
ex = None
for D in up(frozenset([DELTA]), 7):
    if len(D) < 2:
        continue
    if time.time() - T0 > 0.3 * TL:
        st["exhaustive_le7"]["stopped"] = "time"
        break
    r, _ = greatest(D, imgs)
    st["exhaustive_le7"][r] = st["exhaustive_le7"].get(r, 0) + 1
    if r != "ok" and ex is None:
        ex = sorted(map(list, D))
print(json.dumps({"exhaustive_le7": st["exhaustive_le7"], "example": ex, "secs": round(time.time() - T0, 1)}), flush=True)

rnd = random.Random(20260918)


def rand_tree(k):
    L = {DELTA}
    while len(L) < k:
        t = rnd.choice(sorted(L))
        P1, P2 = rnd.choice(splits(t))
        L.remove(t)
        L.add(P1)
        L.add(P2)
    return frozenset(L)


for k in (8, 10, 12, 14, 16, 20, 25, 30, 40, 60, 80):
    for _ in range(150):
        if time.time() - T0 > 0.6 * TL:
            break
        X = rand_tree(k)
        r, nb = greatest(X, imgs)
        st["random"][r] = st["random"].get(r, 0) + 1
        st["random"]["max_below"] = max(st["random"].get("max_below", 0), nb)
        if r != "ok" and "example" not in st["random"]:
            st["random"]["example"] = sorted(map(list, X))
print(json.dumps({"random": st["random"], "secs": round(time.time() - T0, 1)}), flush=True)

for k in (4, 6, 8, 12, 16):
    for _ in range(40):
        if time.time() - T0 > 0.95 * TL:
            break
        info, U = R.run_ore(rand_tree(k), rand_tree(k), calls=60000)
        if U is None:
            continue
        r, nb = greatest(U, imgs)
        st["reversing"][r] = st["reversing"].get(r, 0) + 1
        st["reversing"]["max_size"] = max(st["reversing"].get("max_size", 0), len(U))
        if r != "ok" and "example" not in st["reversing"]:
            st["reversing"]["example"] = sorted(map(list, U))
print(json.dumps({"reversing": st["reversing"], "secs": round(time.time() - T0, 1)}), flush=True)
