#!/usr/bin/env python3
"""Kurosh retract test for the 20 commuting survivors of `linear-bouquet-recursions-ray-loop-and-contraction`
(node `commuting-bouquet-survivors-are-not-finitely-presented`).

For each linear bouquet recursion with [S, T] = 1 and ord S = inf the script checks, exactly:
  (1) sigma = pi_S and tau = pi_T; the level-1 off-ray supports supp_S = {y != z : S|_y != 1}
      and supp_T; S|_z = S and T|_z = T as reduced words;
  (2) [S, T] is trivial in G (R.trivial), o = ord T (R.order: T^o trivial, T^(o/p) not),
      S has infinite order (infinite_order certificate of same_point_screen.py);
  (3) Q_E = section closure of {[S, T], T^o}; each word of Q_E is rewritten in the Nielsen
      basis {a, e, S, T} (s = A^-1 S B^-1, t = C^-1 T D^-1) and tested for being cyclically
      conjugate into F(a, e) or into F(S, T)  ("pure");
  (4) for sigma = tau = 1 and disjoint supports the hand proof of the node gives
      H = <S, T | [S, T], T^o> = Z x C_o; this is reported as 'H-pres hand'.
Run: nice -n 10 timeout 1200 python3 survivor_kurosh.py > survivor_kurosh.out
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "bouquet-ray-loop-2026-09-19"))
sys.path.insert(0, os.path.join(HERE, "..", "loop-graph-screen-2026-09-18"))
from bouquets import bouquets
from loopgraph import N, ID, reduce, inv, fmt
from same_point_screen import infinite_order

def comm(u, v): return reduce(u + v + inv(u) + inv(v))

def nielsen(R, info, w):
    """rewrite a word over {a, e, s, t} in the basis {a, e, S, T}; S, T are new letters."""
    S, T = info["S"], info["T"]
    iS = S.index(("s", 1)); iT = T.index(("t", 1))
    A, B = S[:iS], S[iS + 1:]; C, D = T[:iT], T[iT + 1:]
    sub = {"s": inv(A) + (("S", 1),) + inv(B), "t": inv(C) + (("T", 1),) + inv(D)}
    out = []
    for l, e in w:
        r = sub.get(l, ((l, 1),))
        out.extend(r if e == 1 else inv(r))
    return reduce(out)

def cyc_reduce(w):
    w = list(w)
    while len(w) >= 2 and w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]:
        w = w[1:-1]
    return tuple(w)

def fmtN(w):  # S, T are basis letters here; inverses shown as X'
    return " ".join(l if e == 1 else l + "'" for l, e in w) or "1"

def pure(w):
    letters = {l for l, _ in cyc_reduce(w)}
    if letters <= {"a", "e"}: return "F(a,e)"
    if letters <= {"S", "T"}: return "F(S,T)"
    return None

def main():
    rows = []
    for name, R, info in bouquets():
        S, T, z = info["S"], info["T"], info["z"]
        if not R.trivial(comm(S, T)): continue
        if not infinite_order(R, S): continue
        sig1 = info["sigma"] == ID and info["tau"] == ID
        suppS = sorted(y for y in range(N) if y != z and R.sec(S, y))
        suppT = sorted(y for y in range(N) if y != z and R.sec(T, y))
        loopok = R.sec(S, z) == reduce(S) and R.sec(T, z) == reduce(T)
        o = R.order(T)
        Q = R.closure([comm(S, T), T * o])
        QN = sorted((fmtN(nielsen(R, info, q)), pure(nielsen(R, info, q))) for q in Q)
        allpure = all(p for _, p in QN)
        hand = sig1 and loopok and not (set(suppS) & set(suppT))
        rows.append((name, sig1, suppS, suppT, loopok, o, len(Q), allpure, hand, QN))
    for name, sig1, sS, sT, lok, o, nq, ap, hand, QN in rows:
        print(f"{name} | sigma=tau=1 {sig1} | supp S {sS} supp T {sT} | loops {lok} | ord T {o} | "
              f"|Q_E| {nq} | pure {ap} | H-pres {'hand' if hand else 'NOT hand'}")
        for q, p in QN:
            print(f"    {p or 'MIXED':7s} {q if len(q) < 160 else q[:160] + ' ...'}")
    print("survivors:", len(rows), "| all Q_E pure:", sum(r[7] for r in rows),
          "| pure and H-pres by hand:", sum(r[7] and r[8] for r in rows))

if __name__ == "__main__":
    main()
