"""Independent re-check (reviewer w11-101) of the 2-graph model of V_2(Z/2 wr Z).

Written from scratch; it does not import or reuse two_graph.py.  Differences in method:
  * elements of K = F_2(t) are reduced fractions num/den of F_2[t]-polynomials
    (python ints as bit masks), not Laurent pairs;
  * membership in P is decided from the GEOMETRIC definition via the valuations
    v_pi, v_0, v_inf (a(O) <= O, and a(rho_*) an ancestor of rho_* in T_0 x T_inf),
    never from the closed formula of Lemma 1;
  * P_(m,n) is found by brute force over all b = A / (t^s pi^k) in a box, so
    translation parts with pi-poles or extra t-powers would be detected;
  * unique factorisation is checked EXHAUSTIVELY for all a with d(a) <= (3,3)
    and all p <= d(a);
  * the germ step is checked EXHAUSTIVELY over all mu in P_(M,M), M <= 6;
  * the lamplighter automaton is compared with x -> t x, t x + 1 on O/pi^L O.
"""
import itertools
import random
import sys

T = 0b10      # t
PI = 0b11     # 1 + t


def pmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def pdivmod(a, b):
    q = 0
    db = b.bit_length()
    while a and a.bit_length() >= db:
        s = a.bit_length() - db
        q ^= 1 << s
        a ^= b << s
    return q, a


def pgcd(a, b):
    while b:
        a, b = b, pdivmod(a, b)[1]
    return a


def deg(a):
    return a.bit_length() - 1


def ppow(a, e):
    r = 1
    for _ in range(e):
        r = pmul(r, a)
    return r


class K:
    """Element num/den of F_2(t), reduced, den != 0."""
    __slots__ = ("n", "d")

    def __init__(self, n, d=1):
        if d == 0:
            raise ZeroDivisionError
        if n == 0:
            self.n, self.d = 0, 1
            return
        g = pgcd(n, d)
        self.n, self.d = pdivmod(n, g)[0], pdivmod(d, g)[0]

    def __add__(self, o):
        return K(pmul(self.n, o.d) ^ pmul(o.n, self.d), pmul(self.d, o.d))
    __sub__ = __add__

    def __mul__(self, o):
        return K(pmul(self.n, o.n), pmul(self.d, o.d))

    def inv(self):
        return K(self.d, self.n)

    def __eq__(self, o):
        return self.n == o.n and self.d == o.d

    def __hash__(self):
        return hash((self.n, self.d))

    def iszero(self):
        return self.n == 0


INF = 10 ** 9


def vpoly(a, p):
    if a == 0:
        return INF
    v = 0
    while True:
        q, r = pdivmod(a, p)
        if r:
            return v
        a, v = q, v + 1


def v_pi(x):
    return INF if x.iszero() else vpoly(x.n, PI) - vpoly(x.d, PI)


def v_0(x):
    return INF if x.iszero() else vpoly(x.n, T) - vpoly(x.d, T)


def v_inf(x):
    return INF if x.iszero() else deg(x.d) - deg(x.n)


def tpi(i, j):
    """t^i pi^j as an element of K."""
    n = pmul(ppow(T, max(i, 0)), ppow(PI, max(j, 0)))
    d = pmul(ppow(T, max(-i, 0)), ppow(PI, max(-j, 0)))
    return K(n, d)


def comp(a, c):
    """(a o c)(x) = a(c(x)); maps are pairs (u, b), x -> u x + b."""
    return (a[0] * c[0], a[0] * c[1] + a[1])


def inv(a):
    ui = a[0].inv()
    return (ui, ui * a[1])


def in_P(a):
    u, b = a
    # a(O) = b + u O inside O
    if not (v_pi(u) >= 0 and v_pi(b) >= 0):
        return False
    # T_0: b + u F_2[[t]] contains F_2[[t]]
    if not (v_0(u) <= 0 and v_0(b) >= v_0(u)):
        return False
    # T_inf: {x : v_inf(x - b) >= v_inf(u) + 1} contains {x : v_inf(x) >= 1}
    if not (v_inf(u) <= 0 and v_inf(b) >= v_inf(u) + 1):
        return False
    return True


def degree(a):
    return (-v_0(a[0]), -v_inf(a[0]))


def brute_P(m, n, S=None, Kp=2, D=None):
    """All a in P_(m,n), searched over b = A/(t^s pi^k), 0<=s<=S, 0<=k<=Kp, deg A < D."""
    u = tpi(-m, m + n)
    S = m + 1 if S is None else S
    D = m + n + S + Kp if D is None else D
    found = set()
    for s in range(S + 1):
        for k in range(Kp + 1):
            den = pmul(ppow(T, s), ppow(PI, k))
            for A in range(1 << D):
                b = K(A, den)
                if in_P((u, b)):
                    found.add(b)
    return [(u, b) for b in found]


def ball_key(a, depth):
    """a(O) = b + pi^depth O  ->  b mod pi^depth as a polynomial of degree < depth."""
    b = a[1]
    # b is in O, so den is prime to pi; invert den mod pi^depth
    mod = ppow(PI, depth)
    # extended Euclid for inverse of b.d mod pi^depth
    r0, r1, s0, s1 = mod, pdivmod(b.d, mod)[1], 0, 1
    while r1:
        q, r = pdivmod(r0, r1)
        r0, r1, s0, s1 = r1, r, s1, s0 ^ pmul(q, s1)
    assert r0 == 1
    return pdivmod(pmul(b.n, s0), mod)[1]


def main():
    ok = True
    out = []
    # (1) relations
    one = K(1)
    e = {c: (K(PI, T), K(c, T)) for c in (0, 1)}
    f = {c: (K(PI), K(c)) for c in (0, 1)}
    rel = all(comp(e[i], f[j]) == comp(f[i], e[(i + j) % 2]) for i in (0, 1) for j in (0, 1))
    # no other coincidences between ef and fe words
    ef = {comp(e[i], f[j]) for i in (0, 1) for j in (0, 1)}
    fe = {comp(f[i], e[j]) for i in (0, 1) for j in (0, 1)}
    rel = rel and ef == fe and len(ef) == 4
    out.append(f"(1) e_i f_j = f_i e_(i+j), and the four ef-products are distinct and equal the fe-products: {rel}")
    ok &= rel
    # edges are in P with the right degree
    edg = all(in_P(x) and degree(x) == (1, 0) for x in e.values()) and \
        all(in_P(x) and degree(x) == (0, 1) for x in f.values())
    out.append(f"    edges in P with degrees (1,0),(0,1): {edg}")
    ok &= edg
    # (2) brute-force P_(m,n)
    Ps = {}
    good = True
    for m in range(4):
        for n in range(4):
            L = brute_P(m, n)
            Ps[(m, n)] = L
            keys = {ball_key(a, m + n) for a in L}
            poly_only = all(a[1].d == ppow(T, vpoly(a[1].d, T)) for a in L)
            if len(L) != 2 ** (m + n) or len(keys) != 2 ** (m + n) or not poly_only:
                good = False
                out.append(f"    FAIL at {(m, n)}: {len(L)} elements, {len(keys)} balls")
    out.append(f"(2) brute force (b with pi-poles allowed): |P_(m,n)| = 2^(m+n), translations Laurent polynomials, a->a(O) onto balls, m,n<=3: {good}")
    ok &= good
    # (0,0): trivial units
    triv = Ps[(0, 0)] == [(one, K(0))]
    out.append(f"    P_(0,0) = {{id}}: {triv}")
    ok &= triv
    # (3) exhaustive unique factorisation
    good = True
    cnt = 0
    for (m, n), L in Ps.items():
        for a in L:
            for p in itertools.product(range(m + 1), range(n + 1)):
                q = (m - p[0], n - p[1])
                sols = [ap for ap in Ps[p] if in_P(comp(inv(ap), a)) and degree(comp(inv(ap), a)) == q]
                cnt += 1
                if len(sols) != 1:
                    good = False
    out.append(f"(3) exhaustive unique factorisation, all a with d(a)<=(3,3), all p<=d(a) ({cnt} cases): {good}")
    ok &= good
    # (4) germ step, exhaustive over mu in P_(M,M).
    # Predicted: the rho-condition for g mu does not depend on mu and holds iff M >= M_rho(g), where
    #   T_0  : v_0(u) - M <= 0   and v_0(b)  >= v_0(u) - M,
    #   T_inf: v_inf(u) - M <= 0 and v_inf(b) >= v_inf(u) - M + 1.
    # Check: for M <= 7, among admissible mu (g mu (O) <= O), ALL g mu lie in P if M >= M_rho and NONE if M < M_rho.
    rnd = random.Random(20260918)
    good = True
    rows = []
    cache = {}
    for trial in range(16):
        i, j = rnd.randint(-2, 2), rnd.randint(-2, 2)
        u = tpi(i, j)
        den = pmul(ppow(T, rnd.randint(0, 2)), ppow(PI, rnd.randint(0, 3)))
        b = K(rnd.randrange(1, 1 << 5), den)
        g = (u, b)
        Mr = 0
        while not (v_0(u) - Mr <= 0 and v_0(b) >= v_0(u) - Mr and v_inf(u) - Mr <= 0 and v_inf(b) >= v_inf(u) - Mr + 1):
            Mr += 1
        nadm = []
        for M in range(0, 8):
            if M not in cache:
                cache[M] = list(Ps[(M, M)]) if M <= 3 else brute_P_fast(M)
            adm = [mu for mu in cache[M] if v_pi(comp(g, mu)[1]) >= 0 and v_pi(comp(g, mu)[0]) >= 0]
            nin = sum(in_P(comp(g, mu)) for mu in adm)
            if M >= Mr and nin != len(adm):
                good = False
            if M < Mr and nin != 0:
                good = False
            nadm.append(len(adm))
        rows.append((Mr, nadm[-1]))
    out.append(f"(4) germ step, exhaustive over P_(M,M), M<=7, 16 random g with pi-poles: all admissible g mu in P iff M >= M_rho(g); (M_rho, #admissible at M=7) = {rows}: {good}")
    ok &= good
    # (5) automaton vs affine maps on O / pi^L O
    L = 10
    mod = ppow(PI, L)

    def digits(x):  # x mod pi^L -> pi-adic digits
        ds = []
        for _ in range(L):
            q, r = pdivmod(x, PI)
            ds.append(r)
            x = q
        return tuple(ds)

    def undig(ds):
        x = 0
        for d in reversed(ds):
            x = pmul(x, PI) ^ d
        return x

    def aff(c):  # x -> t x + c on O/pi^L
        return lambda ds: digits(pdivmod(pmul(T, undig(ds)) ^ c, mod)[1])

    # automaton: A = sigma(A, B), B = (A, B) : states act on digit tuples
    def auto(state, ds):
        res = []
        for d in ds:
            if state == 'A':
                res.append(1 - d)
            else:
                res.append(d)
            state = 'A' if d == 0 else 'B'
        return tuple(res)

    # candidate identification: x -> t x + 1  <->  one state, x -> t x  <-> other, possibly after swapping digits
    allpts = list(itertools.product((0, 1), repeat=L))
    match = None
    for swap in (False, True):
        sw = (lambda ds: tuple(1 - d for d in ds)) if swap else (lambda ds: ds)
        for sA, sB in ((1, 0), (0, 1)):
            if all(sw(auto('A', sw(ds))) == aff(sA)(ds) and sw(auto('B', sw(ds))) == aff(sB)(ds) for ds in allpts):
                match = (swap, sA, sB)
    out.append(f"(5) lamplighter automaton a=sigma(a,b), b=(a,b) equals x->tx+c on O/pi^{L} O up to relabelling {match}: {match is not None}")
    ok &= match is not None
    out.append("ALL OK" if ok else "FAILURES")
    print("\n".join(out))
    return 0 if ok else 1


def brute_P_fast(M):
    """P_(M,M) for larger M: search b = A / t^M with deg A < 2M+2 (poles at pi excluded by (2))."""
    u = tpi(-M, 2 * M)
    L = []
    for A in range(1 << (2 * M + 1)):
        b = K(A, ppow(T, M))
        if in_P((u, b)):
            L.append((u, b))
    assert len(L) == 4 ** M
    return L


if __name__ == "__main__":
    sys.exit(main())
