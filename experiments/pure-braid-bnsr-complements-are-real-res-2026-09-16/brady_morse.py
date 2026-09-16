#!/usr/bin/env python3
"""Bestvina-Brady Morse test for BNSR membership of pure braid characters on the dual Garside (Brady) complex.

P_n acts freely and cocompactly on the universal cover X of the Brady complex of B_n: vertices are braids g and
k-simplices are chains g < g x_1 < ... < g x_1...x_k with x_1...x_k a dual simple element (Brady 2001, Bessis 2003;
contractibility is quoted, not re-proved here).  For chi = sum a_ij omega_ij and t: S_n -> R put
    h(g) = sum_{i<j} a_ij W_ij(g) + t[perm(g)],
where W_ij(g) is half the signed number of crossings of the strands starting at i and j.  Then h(p g) = chi(p) + h(g) for
pure p, h is affine on simplices, and the edge increments take finitely many values.  If they are all nonzero and every
ascending link (full subcomplex of the vertex link on higher neighbours) is (m-1)-connected, then [chi] is in Sigma^m(P_n)
(Bestvina-Brady Morse lemma, run on full subcomplexes of vertices above a level).  This script tests the hypothesis of that
criterion for m <= 2: ascending links nonempty, connected, H_1 = 0 over F_2 and F_3, and pi_1 = 1 by a propagation
certificate (spanning tree edges trivial; a triangle with one trivial edge identifies the other two, with signs).
A failure of the test proves nothing.  A pass for m = 2 is a proof of [chi] in Sigma^2 for that chi, conditional on the
correctness of this code and of the quoted structure theory.

The dual simple elements are built as lifts of the noncrossing permutations below c = perm(delta) and checked against the
Artin action on the free group (faithful): lift(w) * band(t) == lift(w t) whenever w t is noncrossing of length l(w)+1.

Usage: timeout 600 python3 brady_morse.py [n]    (writes brady_morse_n<n>.json next to this file)
"""
import itertools, json, os, random, sys, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------- braids ----------
def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def artin(word, n):
    """images of free generators under the automorphism of F_n given by the braid word (letters +-k, k=1..n-1)."""
    img = {i: (i,) for i in range(1, n + 1)}
    for s in word:
        k = abs(s)
        if s > 0:
            loc = {k: (k, k + 1, -k), k + 1: (k,)}
        else:
            loc = {k: (k + 1,), k + 1: (-(k + 1), k, k + 1)}
        # new image: substitute current images into the local rule (anti-homomorphism is fine for equality tests)
        new = dict(img)
        for i, rule in loc.items():
            w = []
            for x in rule:
                w.extend(img[x] if x > 0 else tuple(-y for y in reversed(img[-x])))
            new[i] = reduce_word(w)
        img = new
    return tuple(img[i] for i in range(1, n + 1))


def perm_of(word, n):
    """sigma with sigma[label] = final position (0-based labels/positions)."""
    L = list(range(n))  # L[position] = label
    for s in word:
        k = abs(s) - 1
        L[k], L[k + 1] = L[k + 1], L[k]
    sig = [0] * n
    for p, lab in enumerate(L):
        sig[lab] = p
    return tuple(sig)


def winding2(word, n):
    """2*W[u][v]: signed crossings between strands starting at positions u, v."""
    W = [[0] * n for _ in range(n)]
    L = list(range(n))
    for s in word:
        k = abs(s) - 1
        e = 1 if s > 0 else -1
        u, v = L[k], L[k + 1]
        W[u][v] += e
        W[v][u] += e
        L[k], L[k + 1] = v, u
    return W


def inverse_word(w):
    return tuple(-x for x in reversed(w))


# ---------- permutations (word order product: p*q = first p then q, as position maps) ----------
def pmul(p, q):
    return tuple(q[p[i]] for i in range(len(p)))


def pinv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def ncycles(p):
    seen, c = set(), 0
    for i in range(len(p)):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = p[j]
    return c


def ell(p):
    return len(p) - ncycles(p)


def band_word(s, t):
    """BKL band a_{ts} for 0-based positions s < t: sigma_{t-1}...sigma_{s+1} sigma_s sigma_{s+1}^-1...sigma_{t-1}^-1 (1-based)."""
    S, T = s + 1, t + 1
    up = list(range(T - 1, S, -1))
    return tuple(up + [S] + [-x for x in reversed(up)])


def transposition(n, s, t):
    p = list(range(n))
    p[s], p[t] = t, s
    return tuple(p)


def build_dual(n):
    delta = tuple(range(n - 1, 0, -1))  # sigma_{n-1} ... sigma_1
    c = perm_of(delta, n)
    lc = ell(c)
    allp = list(itertools.permutations(range(n)))
    NC = [w for w in allp if ell(w) + ell(pmul(pinv(w), c)) == lc]
    refl = {}
    for s, t in itertools.combinations(range(n), 2):
        tp = transposition(n, s, t)
        if tp in NC:
            refl[tp] = band_word(s, t)
    ident = tuple(range(n))
    lift = {ident: ()}
    for w in sorted(NC, key=ell):
        if w == ident:
            continue
        for tp, bw in refl.items():
            u = pmul(w, tp)  # w = u * tp
            if u in lift and ell(u) == ell(w) - 1:
                lift[w] = lift[u] + bw
                break
    assert len(lift) == len(NC), "some noncrossing permutation has no reduced factorization"
    checks = 0
    for w in NC:
        for tp, bw in refl.items():
            wt = pmul(w, tp)
            if wt in lift and ell(wt) == ell(w) + 1:
                assert artin(lift[w] + bw, n) == artin(lift[wt], n), ("lift mismatch", w, tp)
                assert perm_of(lift[w] + bw, n) == wt
                checks += 1
    assert artin(lift[c], n) == artin(delta, n), "lift(c) != delta"
    return NC, lift, c, checks


# ---------- vertex link of the Brady complex ----------
def leq(u, v):
    return ell(u) + ell(pmul(pinv(u), v)) == ell(v)


def build_link(n, NC, lift):
    ident = tuple(range(n))
    nontriv = [w for w in NC if w != ident]
    verts = [("+", w) for w in nontriv] + [("-", w) for w in nontriv]
    idx = {v: i for i, v in enumerate(verts)}
    NCset = set(NC)

    def span_ok(bmax, umax):
        p = pmul(bmax, umax)
        return p in NCset and ell(p) == ell(bmax) + ell(umax)

    # chains: a simplex is (neg chain B, pos chain U) with B, U chains in absolute order and span(max B, max U) noncrossing
    # enumerate simplices up to dimension 2 (enough for H_1 and pi_1)
    def comparable(x, y):
        (sx, wx), (sy, wy) = x, y
        if sx == sy:
            return wx != wy and (leq(wx, wy) or leq(wy, wx))
        b, u = (wx, wy) if sx == "-" else (wy, wx)
        return span_ok(b, u)

    V = len(verts)
    adj = [[False] * V for _ in range(V)]
    for i in range(V):
        for j in range(i + 1, V):
            if comparable(verts[i], verts[j]):
                adj[i][j] = adj[j][i] = True

    def is_simplex(ids):
        B = [verts[i][1] for i in ids if verts[i][0] == "-"]
        U = [verts[i][1] for i in ids if verts[i][0] == "+"]
        for X in (B, U):
            for x, y in itertools.combinations(X, 2):
                if not (leq(x, y) or leq(y, x)):
                    return False
        if B and U:
            bmax = max(B, key=ell)
            umax = max(U, key=ell)
            return span_ok(bmax, umax)
        return True

    edges = [(i, j) for i in range(V) for j in range(i + 1, V) if adj[i][j]]
    tris = []
    for i, j in edges:
        for k in range(j + 1, V):
            if adj[i][k] and adj[j][k] and is_simplex((i, j, k)):
                tris.append((i, j, k))
    return verts, edges, tris


# ---------- homology and pi_1 certificate ----------
def rank_mod(rows, p):
    rows = [dict(r) for r in rows if r]
    rank = 0
    pivots = {}
    for r in rows:
        r = {k: v % p for k, v in r.items() if v % p}
        while r:
            col = min(r)
            if col in pivots:
                pr = pivots[col]
                f = r[col] * pow(pr[col], p - 2, p) % p
                for k, v in pr.items():
                    nv = (r.get(k, 0) - f * v) % p
                    if nv:
                        r[k] = nv
                    else:
                        r.pop(k, None)
            else:
                pivots[col] = r
                rank += 1
                break
    return rank


def components(vs, es):
    parent = {v: v for v in vs}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    tree = []
    for (a, b) in es:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
            tree.append((a, b))
    return len({find(v) for v in vs}), tree


def b1_mod(vs, es, ts, p):
    eidx = {e: i for i, e in enumerate(es)}
    d1 = [{a: -1, b: 1} if a != b else {} for (a, b) in es]
    r1 = rank_mod(d1, p)
    d2 = []
    for (a, b, c) in ts:
        d2.append({eidx[(a, b)]: 1, eidx[(b, c)]: 1, eidx[(a, c)]: -1})
    r2 = rank_mod(d2, p)
    return len(es) - r1 - r2


def pi1_certificate(vs, es, ts):
    """True if propagation proves pi_1 = 1 (complex assumed connected)."""
    _, tree = components(vs, es)
    E = {e: i for i, e in enumerate(es)}
    parent = list(range(len(es)))
    sign = [1] * len(es)  # e = root^sign
    TRIV = -1
    trivial = set(E[e] for e in tree)

    def find(x):
        s = 1
        while parent[x] != x:
            s *= sign[x]
            x = parent[x]
        return x, s

    def is_triv(x):
        r, _ = find(x)
        return r in trivial

    def union(x, y, s):  # x = y^s
        rx, sx = find(x)
        ry, sy = find(y)
        if rx == ry:
            return False
        if rx in trivial or ry in trivial:
            if rx in trivial and ry in trivial:
                return False
            trivial.add(rx)
            trivial.add(ry)
            return True
        parent[rx] = ry
        sign[rx] = sx * s * sy
        return True
    changed = True
    while changed:
        changed = False
        for (a, b, c) in ts:
            x, y, z = E[(a, b)], E[(b, c)], E[(a, c)]  # x y = z
            tx, ty, tz = is_triv(x), is_triv(y), is_triv(z)
            if tx + ty + tz >= 2 and tx + ty + tz < 3:
                for e in (x, y, z):
                    if not is_triv(e):
                        r, _ = find(e)
                        trivial.add(r)
                        changed = True
            elif tx:
                changed |= union(y, z, 1)
            elif ty:
                changed |= union(x, z, 1)
            elif tz:
                changed |= union(x, y, -1)
            else:
                rx, sx = find(x)
                rz, sz = find(z)
                ry, sy = find(y)
                if rx == rz and sx == sz:  # y = 1
                    trivial.add(ry); changed = True
                elif ry == rz and sy == sz:  # x = 1
                    trivial.add(rx); changed = True
    return all(is_triv(i) for i in range(len(es)))


def asc_link_status(verts_up, edges, tris):
    vs = sorted(verts_up)
    S = set(vs)
    if not vs:
        return "empty"
    es = [e for e in edges if e[0] in S and e[1] in S]
    ts = [t for t in tris if t[0] in S and t[1] in S and t[2] in S]
    ncomp, _ = components(vs, es)
    if ncomp > 1:
        return "disconnected"
    if b1_mod(vs, es, ts, 2) or b1_mod(vs, es, ts, 3):
        return "H1!=0"
    return "pi1=1" if pi1_certificate(vs, es, ts) else "H1=0,pi1?"


def morse_test(n, a, t, NC, lift, verts, edges, tris, W2, perms):
    """a: dict (i,j) -> value (0-based i<j); t: dict perm -> value. Returns per-type statuses and min |increment|."""
    Sn = list(itertools.permutations(range(n)))
    statuses = {}
    minabs = float("inf")
    for sg in Sn:
        up = []
        for vi, (sgn, w) in enumerate(verts):
            Wm = W2[(sgn, w)]
            inc = sum(val * Wm[sg[i]][sg[j]] for (i, j), val in a.items()) / 2.0
            inc += t.get(pmul(sg, perms[(sgn, w)]), 0.0) - t.get(sg, 0.0)
            minabs = min(minabs, abs(inc))
            if inc > 0:
                up.append(vi)
        statuses[sg] = asc_link_status(up, edges, tris)
    return statuses, minabs


def summarize(st):
    out = {}
    for v in st.values():
        out[v] = out.get(v, 0) + 1
    return out


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t0 = time.time()
    NC, lift, c, checks = build_dual(n)
    verts, edges, tris = build_link(n, NC, lift)
    print(f"n={n}: |NC|={len(NC)}, lift checks={checks}, link: V={len(verts)} E={len(edges)} T={len(tris)}",
          f"{time.time()-t0:.1f}s", flush=True)
    W2, perms = {}, {}
    for sgn, w in verts:
        word = lift[w] if sgn == "+" else inverse_word(lift[w])
        W2[(sgn, w)] = winding2(word, n)
        perms[(sgn, w)] = perm_of(word, n)
    rng = random.Random(20260916)
    pairs = list(itertools.combinations(range(n), 2))
    Sn = list(itertools.permutations(range(n)))
    results = []

    def zero_sum_char(zero_pairs, scale=1000):
        while True:
            a = {p: rng.randint(-scale, scale) for p in pairs}
            for p in zero_pairs:
                a[p] = 0
            free = [p for p in pairs if p not in zero_pairs]
            a[free[-1]] -= sum(a.values())
            if all(a[p] != 0 for p in free):
                return a

    cases = []
    cases.append(("local triple {1,2,3} (resonant, not in Sigma^1)", {(0, 1): 1, (0, 2): 1, (1, 2): -2}))
    cases.append(("generic, nonzero sum (Sigma^infinity)", {p: rng.randint(1, 1000) for p in pairs}))
    cases.append(("generic zero sum (Sigma^{n-3} by Theorem M)", zero_sum_char([])))
    cases.append(("zero sum with c_12 = 0 (the open case)", zero_sum_char([(0, 1)])))
    cases.append(("zero sum with c_12 = 0 (second sample)", zero_sum_char([(0, 1)])))
    trials = int(os.environ.get("TRIALS", "40"))
    for label, a in cases:
        best = None
        for trial in range(trials):
            if trial == 0:
                t = {}
            else:
                scale = rng.choice([1, 10, 100, 1000, 10000])
                t = {sg: rng.uniform(-scale, scale) for sg in Sn}
            st, minabs = morse_test(n, a, t, NC, lift, verts, edges, tris, W2, perms)
            summ = summarize(st)
            good2 = summ.get("pi1=1", 0)
            good1 = sum(v for k, v in summ.items() if k in ("pi1=1", "H1=0,pi1?", "H1!=0"))
            rec = {"trial": trial, "minabs_increment": minabs, "summary": summ, "level1_types": good1,
                   "level2_types": good2}
            if best is None or (minabs > 1e-9, good2, good1) > (best["minabs_increment"] > 1e-9, best["level2_types"],
                                                                 best["level1_types"]):
                best = rec
            if minabs > 1e-9 and good2 == len(Sn):
                break
        verdict = ("criterion passes at level 2" if best["minabs_increment"] > 1e-9 and best["level2_types"] == len(Sn)
                   else "criterion passes at level 1" if best["minabs_increment"] > 1e-9 and best["level1_types"] == len(Sn)
                   else "criterion not met in the trials")
        a_out = {f"{i+1}{j+1}": v for (i, j), v in a.items()}
        results.append({"label": label, "a": a_out, "best": best, "verdict": verdict})
        print(label, a_out, "->", verdict, best["summary"], f"min|inc|={best['minabs_increment']:.3g}",
              f"{time.time()-t0:.1f}s", flush=True)
    with open(os.path.join(HERE, f"brady_morse_n{n}.json"), "w") as f:
        json.dump({"n": n, "seed": 20260916, "trials": trials, "NC": len(NC), "lift_checks": checks,
                   "link": {"V": len(verts), "E": len(edges), "T": len(tris)}, "results": results}, f, indent=1)


if __name__ == "__main__":
    main()
