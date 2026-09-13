#!/usr/bin/env python3
"""Virtual fibring certificates for two-generator one-relator groups G = <a,t | w>.

For each transitive permutation representation of degree k (a subgroup H of index k)
build the covering presentation complex X_H: k vertices, edges a_i: i -> a(i) and
t_i: i -> t(i), and one lift of the relator cell per vertex.  For small characters
phi of H (integer cocycles vanishing on a BFS tree):
  1. Alexander filter: Delta_phi = tau * (t - 1), from the Fox matrix of the
     tree-collapsed complex, must be nonzero with leading and trailing coefficients +-1.
  2. Collapse certificate: integer vertex potentials p with cp = phi + delta p.  In the
     infinite cyclic cover every vertex has one lift per integer height.  The lifts at a
     new top level (vertices at the level, edges whose top endpoint is there, cells whose
     maximum is there) must collapse elementarily, via free edges of cells and then free
     vertices, onto the window below.  The same must hold at a new bottom level (cp negated).
Then the infinite cyclic cover deformation retracts to a finite window, so ker phi is
finitely presented.  Since cd H = 2, Bieri's theorem makes ker phi free, so H is
free-by-cyclic.  For k = 1 and a horizontal generator this is Brown's criterion.
Subgroups come from reps_bt (coset-table backtracking); reps (brute force over S_k)
is kept for --crosscheck.  Every CERT line is re-checked independently by verify.py.
Usage: vfib.py WORD KMAX [RPOT] [LAM] [KMIN]   |   vfib.py --crosscheck WORD KMAX
"""
import sys, itertools, random
from fractions import Fraction
from math import gcd
from collections import Counter

LET = {'a': (0, 1), 'A': (0, -1), 't': (1, 1), 'T': (1, -1)}

def partitions(n, m=None):
    m = n if m is None else m
    if n == 0:
        yield []
        return
    for k in range(min(n, m), 0, -1):
        for rest in partitions(n - k, k):
            yield [k] + rest

def cycle_perm(parts):
    p, s = [], 0
    for k in parts:
        p.extend(range(s + 1, s + k)); p.append(s); s += k
    return tuple(p)

def inverse(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return tuple(q)

def act(gens, w, i):
    for g, e in w:
        i = gens[g][0 if e > 0 else 1][i]
    return i

def canon(a, t):
    k, ai, ti, best = len(a), inverse(a), inverse(t), None
    for s in range(k):
        lab, order, idx = {s: 0}, [s], 0
        while idx < len(order):
            i = order[idx]; idx += 1
            for j in (a[i], ai[i], t[i], ti[i]):
                if j not in lab:
                    lab[j] = len(order); order.append(j)
        key = tuple(lab[a[i]] for i in order) + tuple(lab[t[i]] for i in order)
        if best is None or key < best:
            best = key
    return best

def reps(w, k):
    out, seen = [], set()
    for parts in partitions(k):
        a = cycle_perm(parts); ai = inverse(a)
        for t in itertools.permutations(range(k)):
            gens = ((a, ai), (t, inverse(t)))
            if any(act(gens, w, i) != i for i in range(k)):
                continue
            c = canon(a, t)
            if len(set(c)) and c not in seen:
                # canon labels only the orbit of each start point; transitive iff all k labelled
                if len(c) == 2 * k:
                    seen.add(c); out.append((a, t))
    return out

def reps_bt(w, k):
    """Transitive degree-k representations up to conjugacy, by coset-table backtracking.
    Entries are filled in row-major order and new cosets are created only at the first
    undefined entry, so every complete table is in standard form: each subgroup of
    index k occurs once, and conjugates are merged by canon."""
    R = [(0 if g == 0 else 2) + (0 if e > 0 else 1) for g, e in w]
    L, tab, out, seen = len(R), [[-1] * 4 for _ in range(k)], [], set()

    def setent(c, g, d, trail):
        if tab[c][g] == d and tab[d][g ^ 1] == c:
            return True
        if tab[c][g] != -1 or tab[d][g ^ 1] != -1:
            return False
        tab[c][g] = d; tab[d][g ^ 1] = c; trail.append((c, g)); trail.append((d, g ^ 1))
        return True

    def deduce(n, trail):
        changed = True
        while changed:
            changed = False
            for c in range(n):
                f, i = c, 0
                while i < L and tab[f][R[i]] != -1:
                    f = tab[f][R[i]]; i += 1
                if i == L:
                    if f != c:
                        return False
                    continue
                b, j = c, L - 1
                while j >= i and tab[b][R[j] ^ 1] != -1:
                    b = tab[b][R[j] ^ 1]; j -= 1
                if j < i:
                    if f != b:
                        return False
                elif j == i:
                    if not setent(f, R[i], b, trail):
                        return False
                    changed = True
        return True

    def rec(n):
        pos = next(((c, g) for c in range(n) for g in range(4) if tab[c][g] == -1), None)
        if pos is None:
            if n == k:
                a, t = tuple(tab[i][0] for i in range(k)), tuple(tab[i][2] for i in range(k))
                key = canon(a, t)
                if key not in seen:
                    seen.add(key); out.append((a, t))
            return
        c, g = pos
        for d in list(range(n)) + ([n] if n < k else []):
            trail = []
            if setent(c, g, d, trail) and deduce(max(n, d + 1), trail):
                rec(max(n, d + 1))
            for (x, y) in trail:
                tab[x][y] = -1

    rec(1)
    return out

def cover(w, a, t):
    k, ai, ti = len(a), inverse(a), inverse(t)
    ends = [(i, a[i]) for i in range(k)] + [(i, t[i]) for i in range(k)]
    cells = []
    for s in range(k):
        j, cell = s, []
        for g, e in w:
            P, Pi = (a, ai) if g == 0 else (t, ti)
            if e > 0:
                cell.append((g * k + j, 1)); j = P[j]
            else:
                j = Pi[j]; cell.append((g * k + j, -1))
        assert j == s
        cells.append(cell)
    return ends, cells

def nullspace(M, n):
    rows, piv, r = [[Fraction(x) for x in row] for row in M], [], 0
    for col in range(n):
        if r == len(rows):
            break
        pr = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if pr is None:
            continue
        rows[r], rows[pr] = rows[pr], rows[r]
        iv = rows[r][col]; rows[r] = [x / iv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]; rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        piv.append(col); r += 1
    basis = []
    for fc in [c for c in range(n) if c not in piv]:
        v = [Fraction(0)] * n; v[fc] = Fraction(1)
        for i, pc in enumerate(piv):
            v[pc] = -rows[i][fc]
        den = 1
        for x in v:
            den = den * x.denominator // gcd(den, x.denominator)
        iv = [int(x * den) for x in v]; g = 0
        for x in iv:
            g = gcd(g, abs(x))
        basis.append([x // g for x in iv])
    return basis

def tree_edges(k, ends):
    adj = [[] for _ in range(k)]
    for e, (u, v) in enumerate(ends):
        adj[u].append((e, v)); adj[v].append((e, u))
    seen, tree, st = {0}, set(), [0]
    while st:
        u = st.pop()
        for e, v in adj[u]:
            if v not in seen:
                seen.add(v); tree.add(e); st.append(v)
    return tree

def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p

def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x:
            for j, y in enumerate(q):
                r[i + j] += x * y
    return ptrim(r)

def psub(p, q):
    n = max(len(p), len(q))
    return ptrim([(p[i] if i < len(p) else 0) - (q[i] if i < len(q) else 0) for i in range(n)])

def pdiv(p, q):
    p, q = ptrim(p), ptrim(q)
    if not any(p):
        return [0]
    if len(p) < len(q):
        return None
    r, out = list(p), [0] * (len(p) - len(q) + 1)
    for i in range(len(out) - 1, -1, -1):
        c = r[i + len(q) - 1]
        if c % q[-1]:
            return None
        c //= q[-1]; out[i] = c
        for j, y in enumerate(q):
            r[i + j] -= c * y
    return ptrim(out) if not any(r) else None

def det(M):
    n = len(M)
    if n == 0:
        return [1]
    M, sign, prev = [row[:] for row in M], 1, [1]
    for i in range(n):
        pv = next((r for r in range(i, n) if any(M[r][i])), None)
        if pv is None:
            return [0]
        if pv != i:
            M[i], M[pv] = M[pv], M[i]; sign = -sign
        for r in range(i + 1, n):
            for c in range(i + 1, n):
                M[r][c] = pdiv(psub(pmul(M[r][c], M[i][i]), pmul(M[r][i], M[i][c])), prev)
            M[r][i] = [0]
        prev = M[i][i]
    return M[n - 1][n - 1] if sign > 0 else [-x for x in M[n - 1][n - 1]]

def alexander(cells, c, non):
    col = {f: i for i, f in enumerate(non)}
    f0 = next(f for f in non if c[f] != 0)
    M = []
    for cell in cells:
        h, ent = 0, [dict() for _ in non]
        for e, s in cell:
            if e in col:
                ex = h if s > 0 else h - c[e]
                ent[col[e]][ex] = ent[col[e]].get(ex, 0) + s
            h += s * c[e]
        ent = [{x: v for x, v in d.items() if v} for i, d in enumerate(ent) if non[i] != f0]
        mn = min([x for d in ent for x in d] or [0])
        row = []
        for d in ent:
            p = [0] * (max([x - mn for x in d] or [0]) + 1)
            for x, v in d.items():
                p[x - mn] += v
            row.append(ptrim(p))
        M.append(row)
    D = det(M)
    if not any(D):
        return None
    Q = pdiv(D, [1] * abs(c[f0]))
    assert Q is not None
    while Q and Q[0] == 0:
        Q = Q[1:]
    return Q

def collapses(k, ends, cells, cp, rng, tries=6):
    ne, cellmult, tot0 = len(ends), [], [0] * len(ends)
    for cell in cells:
        h, occ = 0, []
        for e, s in cell:
            h2 = h + s * cp[e]; occ.append((e, max(h, h2))); h = h2
        M, d = max(x for _, x in occ), {}
        for e, top in occ:
            if top == M:
                d[e] = d.get(e, 0) + 1
        cellmult.append(d)
        for e, m in d.items():
            tot0[e] += m
    tops = [(v,) if cp[e] > 0 else (u,) if cp[e] < 0 else (u, v) for e, (u, v) in enumerate(ends)]
    for _ in range(tries):
        tot, aliveC, aliveE, aliveV = tot0[:], set(range(len(cells))), set(range(ne)), set(range(k))
        deg = [0] * k
        for e in range(ne):
            for x in tops[e]:
                deg[x] += 1
        while True:
            fe = [e for e in aliveE if tot[e] == 1]
            if fe:
                e = rng.choice(fe)
                C = next(C for C in aliveC if cellmult[C].get(e, 0) == 1)
                aliveC.discard(C); aliveE.discard(e)
                for e2, m in cellmult[C].items():
                    tot[e2] -= m
                for x in tops[e]:
                    deg[x] -= 1
                continue
            hit = None
            for v in aliveV:
                if deg[v] == 1:
                    e = next(e for e in aliveE if v in tops[e])
                    if tot[e] == 0:
                        hit = (v, e); break
            if hit is None:
                break
            v, e = hit
            aliveV.discard(v); aliveE.discard(e)
            for x in tops[e]:
                deg[x] -= 1
        if not aliveC and not aliveE and not aliveV:
            return True
    return False

def main():
    if sys.argv[1] == '--crosscheck':
        s, KMAX = sys.argv[2], int(sys.argv[3])
        w = [LET[ch] for ch in s]
        for k in range(1, KMAX + 1):
            A = {canon(a, t) for a, t in reps(w, k)}
            B = {canon(a, t) for a, t in reps_bt(w, k)}
            print('XCHECK %s k=%d brute=%d bt=%d equal=%s' % (s, k, len(A), len(B), A == B), flush=True)
        print('SENTINEL_DONE', flush=True)
        return
    s, KMAX = sys.argv[1], int(sys.argv[2])
    R = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    LAM = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    KMIN = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    nofilter = False
    w, rng = [LET[ch] for ch in s], random.Random(1)
    for k in range(KMIN, KMAX + 1):
        rs, b1s, nch, nmon, found = reps_bt(w, k), Counter(), 0, 0, None
        for a, t in rs:
            ends, cells = cover(w, a, t)
            tree = tree_edges(k, ends)
            non = [e for e in range(2 * k) if e not in tree]
            M = [[sum(sg for (e, sg) in cell if e == f) for f in non] for cell in cells]
            null = nullspace(M, len(non))
            b1s[len(null)] += 1
            seen = set()
            for lam in itertools.product(range(-LAM, LAM + 1), repeat=len(null)):
                nz = [x for x in lam if x]
                if not nz or nz[0] < 0:
                    continue
                cn = [sum(l * v[j] for l, v in zip(lam, null)) for j in range(len(non))]
                g = 0
                for x in cn:
                    g = gcd(g, abs(x))
                c = [0] * (2 * k)
                for j, f in enumerate(non):
                    c[f] = cn[j] // g
                if tuple(c) in seen:
                    continue
                seen.add(tuple(c)); nch += 1
                D = alexander(cells, c, non)
                mon = D is not None and abs(D[0]) == 1 and abs(D[-1]) == 1
                if not (mon or nofilter):
                    continue
                nmon += 1
                for p in itertools.product(range(-R, R + 1), repeat=k - 1):
                    pot = (0,) + p
                    cp = [c[e] + pot[v] - pot[u] for e, (u, v) in enumerate(ends)]
                    up = collapses(k, ends, cells, cp, rng)
                    dn = collapses(k, ends, cells, [-x for x in cp], rng)
                    if nofilter and (up or dn):
                        print('HALF %s k=%d up=%s down=%s c=%s pot=%s' % (s, k, up, dn, c, pot), flush=True)
                    if up and dn:
                        found = (a, t, c, pot, cp, D); break
                if found:
                    break
            if found:
                break
        print('K %s k=%d reps=%d b1=%s chars=%d monic=%d cert=%s'
              % (s, k, len(rs), sorted(b1s.items()), nch, nmon, found is not None), flush=True)
        if found:
            a, t, c, pot, cp, D = found
            print('CERT %s k=%d a=%s t=%s c=%s pot=%s cp=%s delta=%s' % (s, k, list(a), list(t), c, list(pot), cp, D), flush=True)
            break
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
