#!/usr/bin/env python3
"""Greedy Perron growth of a window set S in Sch(F/H) with neighbours generated on
the fly (no ball precomputation).  Vertices are canonical coset representatives
(cosets.canon); a vertex is *expanded* when it joins S (its 4 neighbours are
computed).  Candidates are unexpanded vertices adjacent to S; each round adds the
fraction `frac` of candidates with the largest score sum_{w in S, w~x} psi(w).
Floating-point scouting only; no certificate is produced.
Usage: greedy_live.py r0 budget frac tag"""
import sys, json, time
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from cosets import IDENT, GENS, comp, canon


def main():
    r0, budget, frac, tag = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    t0 = time.time()
    idx = {IDENT: 0}
    rep = {0: IDENT}          # reps of unexpanded vertices only
    nbr = {}                  # expanded vertex -> 4 neighbour ids
    dist = [0]
    inS = []

    def expand(v):
        f = rep.pop(v)
        row = []
        for t in GENS:
            c = canon(comp(t, f))
            w = idx.get(c)
            if w is None:
                w = len(dist)
                idx[c] = w
                rep[w] = c
                dist.append(dist[v] + 1)
            row.append(w)
        nbr[v] = row
        # keys of expanded vertices are still needed for dedup; keep them in idx

    S = [0]
    expand(0)
    q = 0
    while q < len(S):  # ball B_r0
        v = S[q]; q += 1
        if dist[v] >= r0:
            continue
        for w in nbr[v]:
            if w not in nbr:
                expand(w)
                S.append(w)
    Sset = set(S)
    hist = []
    v0 = None
    while True:
        order = {v: i for i, v in enumerate(S)}
        rows, cols = [], []
        for v in S:
            i = order[v]
            for w in nbr[v]:
                j = order.get(w)
                if j is not None:
                    rows.append(i); cols.append(j)
        m = len(S)
        As = sp.csr_matrix((np.full(len(rows), 0.25), (rows, cols)), shape=(m, m))
        lam, vec = eigsh(As, k=1, which="LA", tol=1e-10)
        psi = np.abs(vec[:, 0]); lam = float(lam[0])
        md = max(dist[v] for v in S)
        hist.append((m, lam, md, len(dist), time.time() - t0))
        print(m, f"{lam:.6f}", "maxdist", md, "discovered", len(dist), f"t={time.time()-t0:.0f}s", flush=True)
        json.dump(dict(r0=r0, frac=frac, history=hist), open(f"greedy_live_{tag}.json", "w"), indent=1)
        if m >= budget:
            break
        score = {}
        for v in S:
            pv = psi[order[v]]
            for w in nbr[v]:
                if w not in Sset:
                    score[w] = score.get(w, 0.0) + pv
        cand = sorted(score, key=lambda w: -score[w])
        k = max(1, int(frac * len(cand)))
        k = min(k, budget - m)
        for w in cand[:k]:
            expand(w)
            S.append(w); Sset.add(w)
    np.save(f"greedy_live_{tag}_S.npy", np.array(S))


if __name__ == "__main__":
    main()
