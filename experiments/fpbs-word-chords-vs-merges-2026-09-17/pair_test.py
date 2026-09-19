"""Do two non-merge chords (reduced arcs) ever beat two merges?

For random transitive Q (L and K transitive) of size n:
  * rho = exact least number of merges reaching n vertices (up to maxdepth);
  * for every pair of reduced arcs of length <= ell that share a port
    (arcs sharing no port cannot fold with each other or with Gamma_A),
    fold Gamma_A + both arcs and record
      - whether the result has n vertices (then d(Q) <= 2 < rho if rho >= 3);
      - the relation R induced on the vertices of Gamma_A, and the least
        number k(R) of merges whose fold-closure contains R.
    A pair with k(R) >= 3 would be two chords doing the work of three
    merges on Gamma_A.
Usage: python3 pair_test.py n trials ell seed
"""
import sys
import random
from collections import defaultdict
from wordchords import (build_gamma_k, random_q, rho_exact, reduced_arcs,
                        arc_ports, signature, pairs_closure_count)


def run(n, trials, ell, seed, maxdepth=4):
    rng = random.Random(seed)
    tot = defaultdict(int)
    for t in range(trials):
        PA, PB = random_q(n, rng)
        F, tab = build_gamma_k(PA, PB)
        N0 = len(F.par)
        base_sig = signature(F, N0)
        V0 = F.nroots()
        rho = rho_exact(F, n, maxdepth)
        arcs = reduced_arcs(F, tab, ell)
        byport = defaultdict(list)
        for i, arc in enumerate(arcs):
            for pt in set(arc_ports(arc)):
                byport[pt].append(i)
        seen_pairs = set()
        sigs = {}
        full = 0
        npairs = 0
        for pt, L in byport.items():
            for ii in range(len(L)):
                for jj in range(ii, len(L)):
                    i, j = L[ii], L[jj]
                    if (i, j) in seen_pairs:
                        continue
                    seen_pairs.add((i, j))
                    npairs += 1
                    G = F.clone()
                    u, w, v = arcs[i]
                    G.add_arc(u, w, v, tab)
                    u, w, v = arcs[j]
                    G.add_arc(G.find(u), w, G.find(v), tab)
                    if G.nroots() == n:
                        full += 1
                    s = signature(G, N0)
                    if s != base_sig:
                        if s not in sigs:
                            sigs[s] = (i, j, G.nroots())
        # k(R) for each distinct induced relation
        kdist = defaultdict(int)
        worst = None
        for s, (i, j, nr) in sigs.items():
            k = pairs_closure_count(F, n, s, N0, 2)
            key = k if k is not None else '>2'
            kdist[key] += 1
            if k is None:
                worst = (arcs[i], arcs[j], nr)
        print('n', n, 'trial', t, 'V0', V0, 'rho', rho, 'arcs', len(arcs),
              'pairs', npairs, 'full', full, 'distinct_R', len(sigs),
              'k(R) dist', dict(kdist), 'witness>2', worst)
        sys.stdout.flush()


if __name__ == '__main__':
    n = int(sys.argv[1])
    trials = int(sys.argv[2])
    ell = int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    run(n, trials, ell, seed)
