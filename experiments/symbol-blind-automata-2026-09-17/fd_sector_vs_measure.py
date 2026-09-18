"""Finite-defect sector versus measure preservation for symbol-blind selectors.

A selector sigma (set partitions of M -> M, sigma(discrete) = e) defines
tau(x)(g) = x(g sigma(pi_g x)) and the partition map T(P) = psi_P^* P, as in
research/symbol-blind-automata-reduce-to-defect-counting.md.

For every selector over G = Z or G = F2 = <a,b> with memory M, the script checks:
  fd_d : on finitely supported partitions of defect d, supported in the K-ball of
         radius R_d (K = M^-1 M; over Z instead the interval [0, R_d)) and taken
         up to translation, T keeps the defect,
         psibar_P is onto, and distinct G-orbits have distinct image orbits;
  perm : the local rule is e-permutive, i.e. bijective in x_e for every choice of
         the other window values, checked at q = |M| + 1 (enough, since a selector
         only sees the partition of the window);
  mp   : the uniform count #{x in [q]^FM : tau(x)|_F = y} = q^(|FM|-|F|) holds for
         every y, for the listed windows F and alphabet sizes q.
By part 4 of that node, mp at a single q >= 2 on all F is measure preservation, i.e.
the defect-counting identities.  Here mp is only checked on small windows, so a
failure refutes the identities, while a pass is evidence.

Specs must list e first (0 over Z, e over F2).

Usage: python3 fd_sector_vs_measure.py Z 0,1,2,3
       python3 fd_sector_vs_measure.py F2 e,a,b,A
       python3 fd_sector_vs_measure.py minority    (the Z/6 collision at q = 2)
"""
import collections
import itertools
import sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def group(name):
    if name == 'Z':
        return (lambda u, v: u + v), (lambda u: -u), 0, int
    def mul(u, v):
        s = list(u)
        for c in v:
            if s and s[-1] == INV[c]:
                s.pop()
            else:
                s.append(c)
        return ''.join(s)
    return mul, (lambda u: ''.join(INV[c] for c in reversed(u))), '', (lambda t: '' if t == 'e' else t)


def canon(t):
    d = {}
    return tuple(d.setdefault(v, len(d)) for v in t)


def main(gname, spec):
    mul, inv, e, parse = group(gname)
    M = [parse(t) for t in spec.split(',')]
    k = len(M)
    disc = tuple(range(k))
    pats = sorted(set(canon(p) for p in itertools.product(range(k), repeat=k)))
    free = [p for p in pats if 0 < max(p) and p != disc]
    choices = {p: [p.index(c) for c in range(max(p) + 1)] for p in free}
    K = {mul(inv(m1), m2) for m1 in M for m2 in M}

    def ball(R):
        if gname == 'Z':
            return list(range(R))
        b = {e}
        for _ in range(R):
            b |= {mul(u, s) for u in b for s in K}
        return sorted(b, key=str)

    def T(classes, sig):
        cl = {u: i for i, C in enumerate(classes) for u in C}
        N = {mul(u, inv(m)) for u in cl for m in M}
        pre = {}
        for g in N:
            win = [cl.get(mul(g, m), ('s', mul(g, m))) for m in M]
            h = mul(g, M[sig.get(canon(win), 0)])
            pre.setdefault(cl.get(h, ('s', h)), set()).add(g)
        out = []
        for key, S in pre.items():
            if isinstance(key, int):
                S = S | {u for u in classes[key] if u not in N}
            elif key[1] not in N:
                S = S | {key[1]}
            if len(S) > 1:
                out.append(frozenset(S))
        hit = set(pre) | {i for i, C in enumerate(classes) if any(u not in N for u in C)}
        return out, all(i in hit for i in range(len(classes)))

    def norm(Q):
        return min(tuple(sorted(tuple(sorted((mul(inv(u), v) for v in C2), key=str)) for C2 in Q))
                   for C in Q for u in C)

    PARTS = {}

    def parts(d, R):
        if (d, R) not in PARTS:
            pts = ball(R)
            res = []
            def rec(avail, cur, dd):
                if dd == d:
                    res.append(cur)
                    return
                for size in range(2, d - dd + 2):
                    for C in itertools.combinations(avail, size):
                        if cur and str(C[0]) <= str(cur[-1][0]):
                            continue
                        rec([p for p in avail if p not in C], cur + [C], dd + size - 1)
            rec(pts, [], 0)
            seen, reps = set(), []
            for P in res:
                if not any(e in C for C in P):
                    continue
                key = norm(P)
                if key not in seen:
                    seen.add(key)
                    reps.append([frozenset(C) for C in P])
            PARTS[(d, R)] = reps
        return PARTS[(d, R)]

    def fd(sig, d, R):
        images = set()
        for P in parts(d, R):
            Q, onto = T(P, sig)
            if not onto or sum(len(C) - 1 for C in Q) != d:
                return False
            key = norm(Q)
            if key in images:
                return False
            images.add(key)
        return True

    def uniform(sig, F, q):
        E = sorted({mul(f, m) for f in F for m in M}, key=str)
        idx = {u: i for i, u in enumerate(E)}
        wins = [[idx[mul(f, m)] for m in M] for f in F]
        cnt = collections.Counter()
        for x in itertools.product(range(q), repeat=len(E)):
            y = []
            for w in wins:
                vals = [x[i] for i in w]
                y.append(vals[sig.get(canon(vals), 0)])
            cnt[tuple(y)] += 1
        return len(cnt) == q ** len(F) and len(set(cnt.values())) == 1

    ie = M.index(e)

    def permutive(sig):
        q = k + 1
        for rest in itertools.product(range(q), repeat=k - 1):
            outs = set()
            for v in range(q):
                vals = list(rest[:ie]) + [v] + list(rest[ie:])
                outs.add(vals[sig.get(canon(vals), 0)])
            if len(outs) != q:
                return False
        return True

    if gname == 'Z':
        radii = (10, 10, 10)
        windows = [(list(range(6)), 2), (list(range(4)), 3), (list(range(2)), 6)]
    else:
        radii = (1, 1, 1)
        windows = [(['', 'a'], 3), (['', 'a', 'b'], 2), (['', 'b'], 3), (['', 'A', 'b'], 2)]
    tab = collections.Counter()
    for combo in itertools.product(*[range(len(choices[p])) for p in free]):
        sig = {p: choices[p][c] for p, c in zip(free, combo) if choices[p][c]}
        tab['rules'] += 1
        if not fd(sig, 1, radii[0]):
            continue
        tab['fd1'] += 1
        if not fd(sig, 2, radii[1]):
            continue
        tab['fd1+fd2'] += 1
        f3 = fd(sig, 3, radii[2])
        mp = all(uniform(sig, F, q) for F, q in windows)
        pm = permutive(sig)
        tab['fd3=%s mp=%s perm=%s' % (f3, mp, pm)] += 1
        print('  fd3', f3, 'mp', mp, 'perm', pm, {p: str(M[j]) for p, j in sig.items()})
        sys.stdout.flush()
    print(gname, M, 'radii', radii, dict(tab))
    tot = collections.Counter()
    for combo in itertools.product(*[range(len(choices[p])) for p in free]):
        sig = {p: choices[p][c] for p, c in zip(free, combo) if choices[p][c]}
        tot['perm=%s' % permutive(sig)] += 1
    print('  all rules:', dict(tot))
    sys.stdout.flush()


def minority():
    f = lambda a, b, c: c if a == b != c else (b if a == c != b else a)
    img = lambda x: tuple(f(x[i], x[(i + 1) % 6], x[(i + 2) % 6]) for i in range(6))
    x, xp = (0, 0, 1, 0, 1, 1), (0, 1, 0, 0, 0, 0)
    print('minority rule on Z/6, q=2:', x, '->', img(x), ';', xp, '->', img(xp))


if __name__ == '__main__':
    if sys.argv[1] == 'minority':
        minority()
    else:
        main(sys.argv[1], sys.argv[2])
