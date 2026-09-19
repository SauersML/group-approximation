#!/usr/bin/env python3
"""Hypotheses of item 2 of `linear-m11-bouquet-recursions-are-not-finitely-presented`
(finite-edge amalgam obstruction) on all 472 linear bouquet recursions.

For each (name, R, info) from bouquets() (w18 library; basis a, e, S = A s B, T = C t D):
  (B)  bouquet at z: sigma = pi_S and tau = pi_T fix z, S|_z = S and T|_z = T as reduced words;
  (Tb) t is bounded with only its self-loop: t|_x is a rooted word for every x != x_t;
  (Sb) s has no second self-loop and does not re-enter s: every s|_x, x != x_s, lies in F(a, e, t);
  (W)  some s|_x, x != x_s, contains t   (s is the unbounded witness of w17 item 4);
  (L)  level-1 sections of S and T away from z lie in F(a, e, t)  (consequence, checked directly);
  (O)  o = ord T is finite: T^o trivial and T^j nontrivial for every smaller multiple j of the
       root order (R.order scans the multiples upward, so the first hit is the exact order).
Also records ord S (exact_order certificate, or 'inf' from infinite_order, or '?').
Run: nice -n 10 timeout 1200 python3 bouquet_amalgam.py > bouquet_amalgam.out
"""
import os, sys
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "bouquet-ray-loop-2026-09-19"))
sys.path.insert(0, os.path.join(HERE, "..", "loop-graph-screen-2026-09-18"))
from bouquets import bouquets
from loopgraph import N, reduce
from same_point_screen import infinite_order, exact_order

def letters(w): return {l for l, _ in w}

def check(name, R, info):
    S, T, z = info["S"], info["T"], info["z"]
    sig, tau = info["sigma"], info["tau"]
    ps, secs_s = R.states["s"]; pt, secs_t = R.states["t"]
    xs = [x for x, w in secs_s.items() if "s" in letters(w)]
    xt = [x for x, w in secs_t.items() if "t" in letters(w)]
    B = sig[z] == z and tau[z] == z and R.sec(S, z) == reduce(S) and R.sec(T, z) == reduce(T)
    Tb = len(xt) == 1 and all(letters(w) <= {"a", "e"} for x, w in secs_t.items() if x != xt[0])
    Sb = len(xs) == 1 and all(letters(w) <= {"a", "e", "t"} for x, w in secs_s.items() if x != xs[0])
    U = any("t" in letters(w) for x, w in secs_s.items() if x != xs[0])
    L = all(letters(R.sec(W_, y)) <= {"a", "e", "t"} for W_ in (S, T) for y in range(N) if y != z)
    o = R.order(T)
    return B, Tb, Sb, U, L, o

def main():
    n = 0; bad = []; ords = Counter(); sord = Counter()
    for name, R, info in bouquets():
        n += 1
        B, Tb, Sb, U, L, o = check(name, R, info)
        ok = B and Tb and Sb and U and L and o is not None
        ords[o] += 1
        if not ok: bad.append((name, B, Tb, Sb, U, L, o))
        so = exact_order(R, info["S"])
        sord["inf" if so is None and infinite_order(R, info["S"]) else ("finite" if so else "?")] += 1
    print("linear bouquet recursions:", n)
    print("all hypotheses (B, Tb, Sb, U, L, O) hold:", n - len(bad))
    for b in bad: print("FAIL", b)
    print("ord T distribution:", dict(sorted(ords.items(), key=lambda kv: str(kv[0]))))
    print("ord S certificates:", dict(sord))

if __name__ == "__main__":
    main()
