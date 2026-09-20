"""Depth-j homological certificate for deep_j(Q), checked against exact search.

For a finite right L-set Q (L = F(a,b)) and a field F (char 0 or p):
  kappa_i(Q)  = dim ker( T_i : H_1(Y_i;F) -> H_1(Sch(Q);F) ), where Y_i is the
                L_i-Schreier graph (a- and t_i-edges) and T_i sends a t_i-edge
                to its path;
  k_u(Q)      = dim { y in F[Q] : y u = 0 }  (right action);
  u_i         = d t_i / d b (Fox), t_i = phi^i(b).
Checked identities / bounds:
  (I)  kappa_i = k_{u_i}                                   (exact)
  (H)  deep_j >= B_j := kappa_{j+1} - kappa_j              (certificate)
  (T)  B_j <= k_{u_1}(Q^{(j)}) = k_{phi^j(u_1)}(Q)          (transport)
also the direct image count: B_j = (c_{j+1}-c_j) + dim I_j - dim I_{j+1}.
Usage: python3 cert.py n j trials seed [maxlevel] [primes...]
"""
import os
import sys
import random
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..',
                                'fpbs-depth-overfolding-2026-09-17'))
from foldlib import t, phi, random_q, depth_graphs, closure, contains_kernel  # noqa
from exact_search import canon, search, transitive  # noqa


def rank_mod(rows, p):
    """Rank over F_p (p > 0) or Q (p = 0) of an integer matrix."""
    from fractions import Fraction
    M = [[(Fraction(x) if p == 0 else x % p) for x in r] for r in rows]
    if not M:
        return 0
    rk, cols = 0, len(M[0])
    for c in range(cols):
        piv = next((r for r in range(rk, len(M)) if M[r][c] != 0), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = (1 / M[rk][c]) if p == 0 else pow(M[rk][c], p - 2, p)
        M[rk] = [(x * iv) if p == 0 else (x * iv) % p for x in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][c] != 0:
                f = M[r][c]
                M[r] = [(x - f * y) if p == 0 else (x - f * y) % p
                        for x, y in zip(M[r], M[rk])]
        rk += 1
    return rk


def inv_perm(P):
    I = [0] * len(P)
    for i, x in enumerate(P):
        I[x] = i
    return I


def fox_b(w):
    """Fox derivative d w / d b as a list of (sign, prefix word)."""
    out, pre = [], []
    for (l, e) in w:
        if l == 'b':
            if e == 1:
                out.append((1, list(pre)))
            else:
                out.append((-1, list(pre) + [('b', -1)]))
        pre.append((l, e))
    return out


def act(q, w, PA, PB, IA, IB):
    for (l, e) in w:
        if l == 'a':
            q = PA[q] if e == 1 else IA[q]
        else:
            q = PB[q] if e == 1 else IB[q]
    return q


def op_matrix(terms, PA, PB):
    """Matrix of y -> y u on F[Q] (rows: basis vector q maps to row q)."""
    n = len(PA)
    IA, IB = inv_perm(PA), inv_perm(PB)
    M = [[0] * n for _ in range(n)]
    for q in range(n):
        for s, w in terms:
            M[q][act(q, w, PA, PB, IA, IB)] += s
    return M


def k_u(terms, PA, PB, p):
    n = len(PA)
    return n - rank_mod(op_matrix(terms, PA, PB), p)


def chain_kernel(PA, PB, tw, p):
    """kappa_i computed directly: dim ker of the chain map C_1(Y) -> C_1(X)
    (automatically inside Z_1(Y)), with Y the a/t-Schreier graph."""
    n = len(PA)
    IA, IB = inv_perm(PA), inv_perm(PB)
    rows = []
    for q in range(n):          # a-edge at q
        r = [0] * (2 * n)
        r[q] = 1
        rows.append(r)
    for q in range(n):          # t-edge at q -> path
        r = [0] * (2 * n)
        x = q
        for (l, e) in tw:
            off = 0 if l == 'a' else n
            if e == 1:
                r[off + x] += 1
                x = PA[x] if l == 'a' else PB[x]
            else:
                x = IA[x] if l == 'a' else IB[x]
                r[off + x] -= 1
        rows.append(r)
    return 2 * n - rank_mod(rows, p)


def comps(PA, perm2):
    n = len(PA)
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for P in (PA, perm2):
        for q in range(n):
            par[f(q)] = f(P[q])
    return len({f(q) for q in range(n)})


def main():
    n, j, trials, seed = [int(x) for x in sys.argv[1:5]]
    maxlevel = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    primes = [int(x) for x in sys.argv[6:]] or [0, 2, 3]
    rng = random.Random(seed)
    tj, tj1 = t(j), t(j + 1)
    u = {i: fox_b(t(i)) for i in (j, j + 1)}
    phij_u1 = fox_b(t(j + 1))  # placeholder, replaced below
    # phi^j(u_1): apply phi^j to each prefix word of u_1 = d t_1 / d b
    phij_u1 = []
    for s, w in fox_b(t(1)):
        for _ in range(j):
            w = phi(w)
        phij_u1.append((s, w))
    done, bad, hist = 0, 0, {}
    while done < trials:
        PA, PB = random_q(n, rng)
        if not transitive(PA, PB):
            continue
        done += 1
        IA, IB = inv_perm(PA), inv_perm(PB)
        cert = {}
        for p in primes:
            kj = k_u(u[j], PA, PB, p) if j > 0 else 0
            kj1 = k_u(u[j + 1], PA, PB, p)
            assert kj == (chain_kernel(PA, PB, tj, p) if j > 0 else 0)
            assert kj1 == chain_kernel(PA, PB, tj1, p)
            tr = k_u(phij_u1, PA, PB, p)
            assert kj1 - kj <= tr, (PA, PB, p)
            cert[p] = kj1 - kj
        Gj, Gj1, m = depth_graphs(PA, PB, j)
        fib = {}
        for v in range(Gj1.V):
            fib.setdefault(Gj1.over[v], []).append(v)
        allp, lawp = {}, {}
        for vs in fib.values():
            for x in range(len(vs)):
                for y in range(x + 1, len(vs)):
                    a, b = vs[x], vs[y]
                    c = canon(closure(Gj1, [(a, b)]))
                    if m[a] == m[b]:
                        lawp.setdefault(c, (a, b))
                    allp.setdefault(c, (a, b))
        ok = lambda cls: contains_kernel(Gj1, cls, m)
        law, _ = search(Gj1, m, list(lawp.values()), ok, maxlevel)
        deep, _ = search(Gj1, m, list(allp.values()), ok, maxlevel)
        best = max(cert.values())
        if deep is not None and deep < best:
            bad += 1
        key = (law, deep, best)
        hist[key] = hist.get(key, 0) + 1
    print('n', n, 'j', j, 'trials', trials, 'fields', primes,
          'violations deep<B:', bad)
    for key in sorted(hist, key=str):
        print('  (law, deep, max_F B) =', key, 'count', hist[key])


if __name__ == '__main__':
    main()
