#!/usr/bin/env python3
"""Evidence-only search: is some short cyclically reduced presentation in the
AC-neighbourhood of AK(3) thickenable?

State: an unordered pair of non-empty cyclically reduced words on x, y,
modulo cyclic permutation and inversion of each relator and modulo the 8
signed permutations of {x, y} (all of these preserve the presentation complex
up to homeomorphism and commute with AC moves).
Move: r_i -> cyclic reduction of u.v where u is any cyclic permutation of r_i
and v any cyclic permutation of r_j or r_j^-1 (j != i); this is a composite of
AC moves (conjugation, product).  Only states of total length <= CAP are kept.
BFS from AK(3) = <x,y | x^3 y^-4, xyxy^-1x^-1y^-1>, exhaustive within the cap
for THIS move set (it is not the full length-bounded AC graph: conjugation by
elements that are not cyclic subwords is not a move here).
Every visited state is tested with thicken.dfs(variant='orient') on the
canonical cyclically reduced words (non-reduced realisations are NOT tested).
"""
import subprocess
import sys
import time
import thicken as T


def test_batch(states, binary):
    """orient-thickenability of each state; C port (cross-checked in ctest.py) or Python."""
    if binary is None:
        return [T.thickenable(list(p), "orient")[0] for p in states]
    inp = "".join(" ".join(p) + "\n" for p in states)
    out = subprocess.run([binary], input=inp, capture_output=True, text=True, check=True).stdout.split()
    return [out[2 * i] == "1" for i in range(len(states))]

AUTOS = []
for swap in (False, True):
    for sx in (1, -1):
        for sy in (1, -1):
            m = {}
            tx, ty = ("y", "x") if swap else ("x", "y")
            m["x"] = tx if sx == 1 else tx.upper()
            m["y"] = ty if sy == 1 else ty.upper()
            m["X"] = m["x"].swapcase()
            m["Y"] = m["y"].swapcase()
            AUTOS.append(m)


def inv(w):
    return w[::-1].swapcase()


def cycred(w):
    st = []
    for ch in w:
        if st and st[-1] == ch.swapcase():
            st.pop()
        else:
            st.append(ch)
    i, j = 0, len(st) - 1
    while i < j and st[i] == st[j].swapcase():
        i += 1
        j -= 1
    return "".join(st[i:j + 1])


def rots(w):
    return [w[k:] + w[:k] for k in range(len(w))] if w else [w]


def canon_rel(w):
    return min(rots(w) + rots(inv(w)))


def canon(p):
    best = None
    for m in AUTOS:
        q = tuple(sorted(canon_rel("".join(m[c] for c in r)) for r in p))
        if best is None or q < best:
            best = q
    return best


def neighbours(p, cap):
    out = set()
    for i in (0, 1):
        ri, rj = p[i], p[1 - i]
        room = cap - len(rj)
        for u in rots(ri):
            for s in (rj, inv(rj)):
                for v in rots(s):
                    w = cycred(u + v)
                    if 0 < len(w) <= room:
                        out.add(canon((w, rj)))
    return out


def main(cap, binary=None, max_states=3 * 10**6):
    start = canon(("xxxYYYY", "xyxYXY"))
    seen = {start}
    frontier = [start]
    depth = 0
    t0 = time.time()
    by_len = {}
    thick = []
    tested = 0
    complete = True
    while frontier:
        res = test_batch(frontier, binary)
        tested += len(frontier)
        nxt = []
        for p, ok in zip(frontier, res):
            L = len(p[0]) + len(p[1])
            by_len[L] = by_len.get(L, 0) + 1
            if ok:
                thick.append(p)
                print("THICKENABLE", p, flush=True)
            for q in neighbours(p, cap):
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        depth += 1
        print(f"cap={cap} level={depth} visited={len(seen)} next_frontier={len(nxt)} tested={tested} t={time.time()-t0:.1f}s", flush=True)
        frontier = nxt
        if len(seen) > max_states:
            complete = False
            print("state limit reached; search INCOMPLETE", flush=True)
            break
    print("RESULT cap", cap, "complete", complete, "states", len(seen), "tested", tested,
          "by total length", dict(sorted(by_len.items())), "thickenable found", len(thick), flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]), sys.argv[2] if len(sys.argv) > 2 else None)
