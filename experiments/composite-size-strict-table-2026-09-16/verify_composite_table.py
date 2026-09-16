"""Verify the composite-size strict table (swarm, 2026-09-16).

Labels S = (1, a), M = (1, b, c).  Forward table T_f: only nontrivial class
{(1,1), (1,b), (a,c)}.  Reverse table T_r = transpose of T_f: only nontrivial
class {(1,1), (b,1), (c,a)}.  Rules mu: A^M -> A, nu: A^S -> A.

  Dec(T_f):  nu( mu(p(1,.)), mu(p(a,.)) ) = p(1,1)   for p constant on T_f,
  Enc(T_r):  mu( nu(q(1,.)), nu(q(b,.)), nu(q(c,.)) ) = q(1,1)  for q constant on T_r.

Checks (all by direct evaluation unless marked SAT):
  1. explicit product codes are strict for n = 4, 6, 8, 9 (a x b, a,b >= 2);
  2. explicit selector code over {0,1}^2 (value bit chosen by the parity of the
     third input, flipped off the diagonal x_1 != x_b) is strict (n = 4);
  2b. the 2 x 2 product code still fails Enc at every reverse table in which
     (b,1) ~ (1,1) ~ (c,a) and (1,a) is not equivalent to (b,a);
  3. n = 2: exhaustive over all (mu, nu): no strict pair;
  4. rectangle lemma, exhaustive for n = 2, 3: if (D(o,e), D(f,o)) determines o,
     D is a row-constant or a column-constant bijection;
  5. SAT (independent dict encoder, CaDiCaL): no strict pair for n = 3 and n = 5.
Usage: python3 verify_composite_table.py [--sat]
"""
import itertools, sys, time

S = ['1', 'a']
M = ['1', 'b', 'c']
TF = {('1', '1'): 0, ('1', 'b'): 0, ('a', 'c'): 0, ('1', 'c'): 1, ('a', '1'): 2, ('a', 'b'): 3}
TR = {(m, s): TF[(s, m)] for (s, m) in TF}  # transpose
NCLS = 4
O = TF[('1', '1')]


def dec(mu, nu, n):
    for p in itertools.product(range(n), repeat=NCLS):
        relays = tuple(mu[tuple(p[TF[(s, m)]] for m in M)] for s in S)
        if nu[relays] != p[O]:
            return False
    return True


def enc_witness(mu, nu, n):
    for q in itertools.product(range(n), repeat=NCLS):
        relays = tuple(nu[tuple(q[TR[(m, s)]] for s in S)] for m in M)
        if mu[relays] != q[O]:
            return q
    return None


def tabulate(f, arity, n):
    return {x: f(*x) for x in itertools.product(range(n), repeat=arity)}


def product_code(nb, nc):
    n = nb * nc
    beta = lambda x: x // nc
    gamma = lambda x: x % nc
    sym = lambda b, g: b * nc + g

    def mu(x1, xb, xc):
        if x1 == xb:
            return sym(beta(xc), gamma(x1))
        return sym(beta(xc), (gamma(x1) + 1) % nc)

    def nu(y1, ya):
        return sym(beta(ya), gamma(y1))

    return n, tabulate(mu, 3, n), tabulate(nu, 2, n)


def selector_code():
    n = 4
    bits = lambda x: (x >> 1, x & 1)
    sym = lambda t, v: (t << 1) | v

    def mu(x1, xb, xc):
        z = bits(xc)
        t = z[0] ^ z[1]
        if x1 == xb:
            return sym(t, bits(x1)[t])
        return sym(t, 1 - bits(x1)[t])  # off-diagonal twist; relay 1 never reads x1 != xb

    def nu(y1, ya):
        t, v = bits(y1)
        par = bits(ya)[0]
        o = [0, 0]
        o[t] = v
        o[1 - t] = v ^ par
        return sym(o[0], o[1])

    return n, tabulate(mu, 3, n), tabulate(nu, 2, n)


def check_explicit():
    for (nb, nc) in [(2, 2), (2, 3), (3, 2), (2, 4), (3, 3)]:
        n, mu, nu = product_code(nb, nc)
        d = dec(mu, nu, n)
        w = enc_witness(mu, nu, n)
        print(f"product code {nb}x{nc} (n={n}): Dec={d}, Enc witness={w}")
        assert d and w is not None
    n, mu, nu = selector_code()
    d = dec(mu, nu, n)
    w = enc_witness(mu, nu, n)
    print(f"selector code (n=4): Dec={d}, Enc witness={w}")
    assert d and w is not None


def reverse_family():
    """All reverse tables with (b,1) ~ (1,1) ~ (c,a) and (1,a) not ~ (b,a)."""
    cells = [('1', '1'), ('1', 'a'), ('b', '1'), ('b', 'a'), ('c', '1'), ('c', 'a')]

    def parts(k):
        def rec(i, cur, mx):
            if i == k:
                yield tuple(cur)
                return
            for c in range(mx + 1):
                cur.append(c)
                yield from rec(i + 1, cur, mx + 1 if c == mx else mx)
                cur.pop()
        yield from rec(0, [], 0)

    for P in parts(len(cells)):
        T = dict(zip(cells, P))
        if T[('b', '1')] == T[('1', '1')] == T[('c', 'a')] and T[('1', 'a')] != T[('b', 'a')]:
            yield T


def check_reverse_family():
    """The 2 x 2 product code fails Enc at every reverse table of the family (so do its finer tables)."""
    global TR, NCLS
    saved = (TR, NCLS)
    n, mu, nu = product_code(2, 2)
    count = 0
    for T in reverse_family():
        classes = sorted(set(T.values()))
        TR = {c: classes.index(T[c]) for c in T}
        NCLS = max(len(classes), max(TF.values()) + 1)
        # Enc must fail; Dec is unchanged (it reads only TF)
        found = None
        for q in itertools.product(range(n), repeat=len(classes)):
            relays = tuple(nu[tuple(q[TR[(m, s)]] for s in S)] for m in M)
            if mu[relays] != q[TR[('1', '1')]]:
                found = q
                break
        assert found is not None, T
        count += 1
    TR, NCLS = saved
    print(f"reverse family: product code 2x2 fails Enc at all {count} reverse tables")


def check_n2_exhaustive():
    n = 2
    Mt = list(itertools.product(range(n), repeat=3))
    St = list(itertools.product(range(n), repeat=2))
    strict = 0
    decs = 0
    for muv in itertools.product(range(n), repeat=len(Mt)):
        mu = dict(zip(Mt, muv))
        for nuv in itertools.product(range(n), repeat=len(St)):
            nu = dict(zip(St, nuv))
            if dec(mu, nu, n):
                decs += 1
                if enc_witness(mu, nu, n) is not None:
                    strict += 1
    print(f"n=2 exhaustive: {decs} Dec solutions, {strict} strict")
    assert strict == 0


def determines(D, n):
    seen = {}
    for o, e, f in itertools.product(range(n), repeat=3):
        key = (D[o][e], D[f][o])
        if seen.setdefault(key, o) != o:
            return False
    return True


def trivial(D, n):
    rowconst = all(len(set(D[x])) == 1 for x in range(n)) and len(set(D[x][0] for x in range(n))) == n
    colconst = all(len(set(D[x][z] for x in range(n))) == 1 for z in range(n)) and len(set(D[0])) == n
    return rowconst or colconst


def check_lemma(n):
    good = 0
    for vals in itertools.product(range(n), repeat=n * n):
        D = [vals[i * n:(i + 1) * n] for i in range(n)]
        if determines(D, n):
            good += 1
            assert trivial(D, n), D
    print(f"rectangle lemma n={n}: {good} determining matrices, all row- or column-constant bijections")


def sat_no_strict(n):
    from pysat.solvers import Cadical153
    var = {}

    def v(key):
        if key not in var:
            var[key] = len(var) + 1
        return var[key]

    cl = []
    Mt = list(itertools.product(range(n), repeat=3))
    St = list(itertools.product(range(n), repeat=2))
    for kind, tups in (('mu', Mt), ('nu', St)):
        for x in tups:
            lits = [v((kind, x, s)) for s in range(n)]
            cl.append(lits)
            cl.extend([-lits[i], -lits[j]] for i in range(n) for j in range(i + 1, n))
    for p in itertools.product(range(n), repeat=NCLS):
        rows = [tuple(p[TF[(s, m)]] for m in M) for s in S]
        for y in St:
            cl.append([-v(('mu', rows[k], y[k])) for k in range(2)] + [v(('nu', y, p[O]))])
    # not Enc, with q(1,1) = 0 without loss of generality (conjugate mu, nu by a permutation of A)
    elits = []
    for q in itertools.product(range(n), repeat=NCLS):
        if q[O] != 0:
            continue
        rows = [tuple(q[TR[(m, s)]] for s in S) for m in M]
        e = v(('e', q))
        elits.append(e)
        for z in Mt:
            cl.append([-e] + [-v(('nu', rows[k], z[k])) for k in range(3)] + [-v(('mu', z, 0))])
    cl.append(elits)
    t = time.time()
    with Cadical153(bootstrap_with=cl) as s:
        ok = s.solve()
    print(f"SAT n={n}: strict pair exists = {ok} ({len(var)} vars, {len(cl)} clauses, {time.time() - t:.1f}s)")
    return ok


if __name__ == '__main__':
    check_explicit()
    check_reverse_family()
    check_n2_exhaustive()
    check_lemma(2)
    check_lemma(3)
    if '--sat' in sys.argv:
        assert sat_no_strict(3) is False
        assert sat_no_strict(5) is False
        assert sat_no_strict(4) is True
    print("all checks passed")
