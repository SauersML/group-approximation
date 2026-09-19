"""Domination test for general folded graphs over a finite L-set Q.

Gamma = Stallings fold (over Q) of a bouquet of random words at real
vertices, keeping only graphs that reach every point of Q and are connected.
rho = exact least number of merges folding Gamma onto the Schreier graph of Q;
then every pair of reduced arcs sharing a port (length <= ell) is tested.
Any pair giving n vertices while rho >= 3 is a counterexample to
"k chords are dominated by k merges".
Usage: python3 general_test.py n trials ell nwords wordlen seed
"""
import sys
import random
from collections import defaultdict
from wordchords import (Folder, tables, rho_exact, reduced_arcs, arc_ports,
                        signature, pairs_closure_count)


def random_perm(n, rng):
    p = list(range(n))
    rng.shuffle(p)
    return p


def random_word(length, rng):
    w = []
    while len(w) < length:
        l = rng.randrange(4)
        if w and l == (w[-1] ^ 1):
            continue
        w.append(l)
    return w


def build_random_gamma(PA, PB, nwords, wordlen, rng):
    tab = tables(PA, PB)
    n = len(PA)
    F = Folder()
    for p in range(n):
        F.new(p, True)
    for _ in range(nwords):
        p = rng.randrange(n)
        w = random_word(rng.randint(1, wordlen), rng)
        x = p
        for l in w:
            x = tab[l][x]
        F.add_arc(p, w, x, tab)
    return F, tab


def connected_and_onto(F, n):
    roots = F.roots()
    if {F.phi[r] for r in roots} != set(range(n)):
        return False
    # edge-surjective onto the Schreier graph, so Gamma_Q is a quotient
    cov = {(F.phi[r], l) for r in roots for l in F.out[r]}
    if len(cov) != 4 * n:
        return False
    seen = {roots[0]}
    st = [roots[0]]
    while st:
        u = st.pop()
        for l, t in F.out[u].items():
            t = F.find(t)
            if t not in seen:
                seen.add(t)
                st.append(t)
    # incoming edges are stored as inverse labels, so out covers both
    return len(seen) == len(roots)


def compact(F):
    """Re-index the roots of F into a fresh Folder (drops dead indices)."""
    roots = F.roots()
    idx = {r: i for i, r in enumerate(roots)}
    G = Folder()
    for r in roots:
        G.new(F.phi[r], F.real[r])
    for r in roots:
        for l, t in F.out[r].items():
            G.out[idx[r]][l] = idx[F.find(t)]
    return G


def run(n, trials, ell, nwords, wordlen, seed):
    rng = random.Random(seed)
    done = 0
    hist = defaultdict(int)
    while done < trials:
        PA = random_perm(n, rng)
        PB = random_perm(n, rng)
        F, tab = build_random_gamma(PA, PB, nwords, wordlen, rng)
        if not connected_and_onto(F, n):
            continue
        F = compact(F)
        N0 = len(F.par)
        rho = rho_exact(F, n, 4)
        if rho is None or rho < 3:
            hist[rho] += 1
            continue
        done += 1
        arcs = reduced_arcs(F, tab, ell)
        byport = defaultdict(list)
        for i, arc in enumerate(arcs):
            for pt in set(arc_ports(arc)):
                byport[pt].append(i)
        seen = set()
        full = 0
        worst = 0
        wit = None
        base = signature(F, N0)
        sigs = {}
        for pt, Lst in byport.items():
            for ii in range(len(Lst)):
                for jj in range(ii, len(Lst)):
                    i, j = Lst[ii], Lst[jj]
                    if (i, j) in seen:
                        continue
                    seen.add((i, j))
                    G = F.clone()
                    u, w, v = arcs[i]
                    G.add_arc(u, w, v, tab)
                    u, w, v = arcs[j]
                    G.add_arc(G.find(u), w, G.find(v), tab)
                    if G.nroots() == n:
                        full += 1
                        wit = (arcs[i], arcs[j])
                    s = signature(G, N0)
                    if s != base and s not in sigs:
                        sigs[s] = (i, j)
        kd = defaultdict(int)
        kwit = None
        for s, (i, j) in sigs.items():
            k = pairs_closure_count(F, n, s, N0, 2)
            kd[k if k is not None else '>2'] += 1
            if k is None:
                kwit = (arcs[i], arcs[j])
        print('n', n, 'V', N0, 'rho', rho, 'arcs', len(arcs), 'pairs', len(seen),
              'full', full, 'wit', wit, 'k(R)', dict(kd), 'kwit', kwit)
        sys.stdout.flush()
    print('skipped rho histogram', dict(hist))


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    run(*a)
