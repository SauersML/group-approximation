"""Exact census of generating double cosets via vertex identifications.

Lemma (artifact §1): if H <= F(a,b) has folded based Stallings graph Delta and
<H, t> = F, then t lies in H g_p g_q^{-1} H for an ordered pair p != q of vertices of
Delta such that Delta/(p ~ q) folds to the one-vertex rose; g_p is any word read
in Delta from the base to p.  This script lists all pairs for H = <a, b_{m-d}>
in F(a, b_m) and tests whether g_p g_q^{-1} lies in H b H or H B H.
"""
import sys
from collections import deque
from fg import Subgroup, Folded, red, inv
from packing import w_stage


def spanning_words(g, base):
    words = {base: ""}
    dq = deque([base])
    while dq:
        v = dq.popleft()
        for (u, x), y in g.adj.items():
            if u == v and y not in words:
                words[y] = words[v] + x
                dq.append(y)
    return words


def main(dmax):
    for d in range(1, dmax + 1):
        w = w_stage(d)
        H = Subgroup(["a", w])
        g = H.g
        o = g.at("o")
        gw = spanning_words(g, o)
        verts = sorted(gw)
        gen_pairs = bad = 0
        badlist = []
        for p in verts:
            for q in verts:
                if p == q:
                    continue
                t = red(gw[p] + inv(gw[q]))
                # Delta/(p~q) is the fold of Delta with the loop t at the base.
                if not H.generates_F2_with(t):
                    continue
                gen_pairs += 1
                if not (H.in_double_coset("b", t) or H.in_double_coset("B", t)):
                    bad += 1
                    badlist.append(t)
        print(f"d={d} |w|={len(w)} |V(Delta)|={len(verts)} generating ordered pairs={gen_pairs} "
              f"outside H b^+-1 H={bad} {badlist[:5]}")
        sys.stdout.flush()


if __name__ == "__main__":
    main(int(sys.argv[1]))
