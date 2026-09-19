#!/usr/bin/env python3
"""Machine-check the derivations of
research/artifacts/zp-houghton-h3-families-via-reroute-2026-09-18.md.

Conventions as in research/artifacts/zp-houghton-pours-2026-09-17.md, Section 0,
with n = 3 and rays 1, 2, 3: points (x, p), p >= 1; words act on the right and
are read left to right.
  lam(x,y): (x,p)->(x,p-1) for p>=2, (x,1)->(y,1), (y,p)->(y,p+1).
  tau(x):   swaps (x,1),(x,2).

A word is a list of tokens (name, sign), name 'lxy' or 'tx', sign +1 or -1
(sign -1 is the FORMAL inverse letter).  A derivation starts from a word and
applies steps until the word is empty:

  free   cancel an adjacent pair (s,+1)(s,-1) or (s,-1)(s,+1): cost 0;
  Q      replace a subword u by a word v with |u| + |v| <= 40 and u = v in
         H_3.  Then u v^(-1) is a trivial word of length <= 40, a relator of
         the set Q of the presentation P: cost 1;
  macro  replace a subword u by v, where u v^(-1) is (freely) one of the cited
         relations.  The script checks that u and v are LITERALLY the two sides
         of that relation, and that u = v in H_3:
           A[a,b,c](k):  lam_ac^k lam_cb^k  <->  N_k (two-ray word in a,b)
           R3(m):        D^u_x(m)           <->  D^v_x(m),  {x,u,v} = {1,2,3}
           D3(j):        lam_wz Ed(t_x(j)) lam_zw  <->  Ed(t_x(j))
           F'(k):        the whole word tau_x D^u_x(k) tau_x D^u_x(k) -> empty
  conj   replace the word W by g W g^(-1) (formal inverse): area unchanged.

Equality in H_3 of words u, v is decided on every point of depth <= R with
R = max(|u|,|v|) + 3: a point of larger depth stays at depth >= 3 while either
word acts, so it is moved by a pure translation, and depth R pins it down.

For every labeling, every route function c, and all small indices, the script
runs the derivations of the note, checks that each ends at the empty word, and
checks the Q-step counts against the stated bounds:
  (R)  R3(k)     <= 2 A(k) + |N_k| + 4k + 2
  (F)  F'(k)     <= 2 R3(k-2) + 4k + 4                       (k >= 2)
  (F3) F3(k)     <= F'(k) + 2k + 2
  (D)  D3(j)     <= R3(j) + R3(j-1) + 4                      (j >= 1)
  (B)  B3(i,j)   <= 2R3(i-1) + 2R3(j-1) + 2R3(i+j-2) + 8(i+j)
  (C)  C3(j)     <= 2 D3(j) + 2R3(j-1) + 2R3(j-2) + 2 F'(j) + 12 j + 8
(the macro multiset of each run is printed; a macro absent from a run costs 0).
"""
import itertools
import sys

RAYS = (1, 2, 3)


def lam(x, y):
    return 'l%d%d' % (x, y)


def tau(x):
    return 't%d' % x


def act_letter(name, sign, pt):
    r, p = pt
    if name[0] == 't':
        x = int(name[1])
        if r == x and p in (1, 2):
            return (x, 3 - p)
        return pt
    x, y = int(name[1]), int(name[2])
    if sign < 0:
        x, y = y, x
    if r == x:
        return (x, p - 1) if p >= 2 else (y, 1)
    if r == y:
        return (y, p + 1)
    return pt


def act(word, pt):
    for name, sign in word:
        pt = act_letter(name, sign, pt)
    return pt


def equal(u, v):
    R = max(len(u), len(v)) + 3
    return all(act(u, (x, p)) == act(v, (x, p)) for x in RAYS for p in range(1, R + 1))


def pos(*names):
    return [(n, 1) for n in names]


def inv(word):
    return [(n, -s) for n, s in reversed(word)]


def D(x, u, m):
    """D^u_x(m) = lam_xu^m tau_x lam_ux^m, represents ((x,m+1),(x,m+2))."""
    return pos(*([lam(x, u)] * m + [tau(x)] + [lam(u, x)] * m))


def Ed_t(c, x, j):
    return D(x, c[x], j - 1)


def Ed_s(p, q):
    """Ed(sigma) with tau-ray p: lam_qp tau_p lam_pq, represents ((p,1),(q,1))."""
    return pos(lam(q, p), tau(p), lam(p, q))


def comm(U, V):
    """[U,V] = U V U^(-1) V^(-1), the convention of the pours note, Section 4."""
    return U + V + inv(U) + inv(V)


# ---------- the two-ray words N_k of the pour-doubling note, Section 2 ----------

def table(a, b):
    lab, lba, ta, tb = lam(a, b), lam(b, a), tau(a), tau(b)
    DH = {lab: [lab, lab, tb], lba: [lba, lba, ta],
          ta: [lab, ta, lab, ta, tb, lba, ta, lba],
          tb: [lba, tb, lba, ta, tb, lab, tb, lab]}
    PSI = {lab: [ta, lab], lba: [lba, ta], ta: [lab, ta, lba], tb: [tb]}
    return DH, PSI


_NCACHE = {}


def N(a, b, k):
    key = (a, b, k)
    if key in _NCACHE:
        return _NCACHE[key]
    DH, PSI = table(a, b)
    if k == 1:
        w = [lam(a, b)]
    elif k % 2 == 0:
        w = [t for s in N(a, b, k // 2) for t in DH[s]]
    else:
        w = [t for s in N(a, b, k - 1) for t in PSI[s]] + [lam(a, b)]
    _NCACHE[key] = w
    return w


def pour(a, b, c, k):
    return pos(*([lam(a, c)] * k + [lam(c, b)] * k))


# ---------- derivations ----------

class Fail(Exception):
    pass


class Deriv:
    def __init__(self, word, tag):
        self.w = list(word)
        self.q = 0
        self.macros = []
        self.tag = tag

    def fail(self, msg):
        raise Fail('%s: %s; word = %s' % (self.tag, msg, self.w))

    def at(self, i, old):
        if self.w[i:i + len(old)] != old:
            self.fail('subword mismatch at %d: want %s' % (i, old))

    def find(self, old, start=0):
        n = len(old)
        for i in range(start, len(self.w) - n + 1):
            if self.w[i:i + n] == old:
                return i
        self.fail('subword not found: %s' % old)

    def Q(self, i, old, new):
        self.at(i, old)
        if len(old) + len(new) > 40:
            self.fail('Q step too long')
        if not equal(old, new):
            self.fail('Q step not an identity: %s -> %s' % (old, new))
        self.w[i:i + len(old)] = new
        self.q += 1

    def macro(self, i, old, new, label):
        self.at(i, old)
        if not equal(old, new):
            self.fail('macro not an identity: %s' % label)
        self.w[i:i + len(old)] = new
        self.macros.append(label)

    def free(self):
        changed = True
        while changed:
            changed = False
            for i in range(len(self.w) - 1):
                (n1, s1), (n2, s2) = self.w[i], self.w[i + 1]
                if n1 == n2 and s1 == -s2:
                    del self.w[i:i + 2]
                    changed = True
                    break

    def normalize(self):
        """Turn every formal inverse letter into a positive letter (1 Q each)."""
        for i, (n, s) in enumerate(self.w):
            if s < 0:
                new = (('l' + n[2] + n[1]) if n[0] == 'l' else n, 1)
                self.Q(i, [(n, s)], [new])

    def cancel_positive(self):
        """Cancel adjacent positive pairs lam_xy lam_yx or tau tau (1 Q each)."""
        changed = True
        while changed:
            changed = False
            self.free()
            for i in range(len(self.w) - 1):
                (n1, s1), (n2, s2) = self.w[i], self.w[i + 1]
                if s1 == s2 == 1 and ((n1[0] == 't' and n1 == n2) or
                                      (n1[0] == 'l' and n2 == 'l' + n1[2] + n1[1])):
                    self.Q(i, self.w[i:i + 2], [])
                    changed = True
                    break

    def conj(self, g):
        self.w = g + self.w + inv(g)

    def done(self):
        self.free()
        if self.w:
            self.fail('not empty at the end')
        return self


def reroute(d, i, x, u, v, m):
    """Replace the literal D^u_x(m) at position i by D^v_x(m) (macro R3(m))."""
    if u == v or m == 0:
        d.at(i, D(x, u, m))
        return
    d.macro(i, D(x, u, m), D(x, v, m), 'R3(%d)' % m)


def commute_single(d, t, X):
    """Word t X t X (t a tau letter whose ray is outside the ray support of the
    positive D-word X): move t across X, cancel t t, cancel X X."""
    L = len(X)
    d.at(0, t + X + t + X)
    for i in range(L):
        d.Q(i, [t[0], X[i]], [X[i], t[0]])
    d.Q(L, t + t, [])
    d.cancel_positive()


def third(x, y):
    return ({1, 2, 3} - {x, y}).pop()


def deriv_R3(x, u, v, k):
    """(R) D^u_x(k) D^v_x(k)^(-1)."""
    d = Deriv(D(x, u, k) + inv(D(x, v, k)), 'R3 x=%d u=%d v=%d k=%d' % (x, u, v, k))
    d.normalize()                                       # 2k+1 conversions
    Nk = pos(*N(u, v, k))
    d.macro(k + 1, pour(u, v, x, k), Nk, 'A[%d,%d,%d](%d)' % (u, v, x, k))
    t = pos(tau(x))
    for i in range(len(Nk)):                            # tau_x across N_k
        d.Q(k + i, [t[0], Nk[i]], [Nk[i], t[0]])
    d.Q(k + len(Nk), t + t, [])
    d.macro(k, Nk, pour(u, v, x, k), 'A[%d,%d,%d](%d)' % (u, v, x, k))
    d.cancel_positive()                                 # 2k pairs
    d.done()
    bound = len(Nk) + 4 * k + 2
    assert d.q <= bound, (d.tag, d.q, bound)
    return d


def deriv_Fprime(x, u, k):
    """(F) tau_x D^u_x(k) tau_x D^u_x(k), k >= 2, conjugated by lam_ux^2."""
    w = third(x, u)
    Dk = D(x, u, k)
    d = Deriv(pos(tau(x)) + Dk + pos(tau(x)) + Dk, "F' x=%d u=%d k=%d" % (x, u, k))
    d.conj(pos(lam(u, x), lam(u, x)))
    d.normalize()                                       # 2 conversions
    two_in = pos(lam(u, x), lam(u, x), tau(x), lam(x, u), lam(x, u))
    d.Q(0, two_in, pos(tau(u)))                         # prefix -> tau_u
    i = d.find(two_in, 1)
    d.Q(i, two_in, pos(tau(u)))                         # middle tau_x -> tau_u
    n = len(d.w)
    d.Q(n - 4, pos(lam(u, x), lam(u, x), lam(x, u), lam(x, u)), [])   # tail
    m = k - 2
    Dm = D(x, u, m)
    d.at(0, pos(tau(u)) + Dm + pos(tau(u)) + Dm)
    reroute(d, 1, x, u, w, m)
    reroute(d, 2 + len(Dm), x, u, w, m)
    commute_single(d, pos(tau(u)), D(x, w, m))
    d.done()
    assert d.q <= 4 * k + 4, (d.tag, d.q)
    return d


def deriv_F3(c, x, k):
    """(F3) [tau_x, D^(c(x))_x(k)] -> normalized F' word."""
    d = Deriv(comm(pos(tau(x)), D(x, c[x], k)), 'F3 x=%d k=%d' % (x, k))
    d.normalize()
    assert d.q <= 2 * k + 2
    d.at(0, pos(tau(x)) + D(x, c[x], k) + pos(tau(x)) + D(x, c[x], k))
    d.macro(0, list(d.w), [], "F'(%d)" % k)
    return d.done()


def deriv_D3(c, x, z, w, j):
    """(D) lam_wz Ed(t_x(j)) lam_zw Ed(t_x(j))^(-1), {x,z,w} = {1,2,3}, j >= 1."""
    V = Ed_t(c, x, j)
    d = Deriv(pos(lam(w, z)) + V + pos(lam(z, w)) + inv(V),
              'D3 c=%s x=%d z=%d w=%d j=%d' % (c, x, z, w, j))
    d.Q(0, pos(lam(w, z)), pos(lam(w, x), lam(x, z)))
    d.Q(2 + len(V), pos(lam(z, w)), pos(lam(z, x), lam(x, w)))
    # inner: lam_xz . D . lam_zx pushes ray x (route z needed)
    reroute(d, 2, x, c[x], z, j - 1)
    # now lam_wx [lam_xz D^z_x(j-1) lam_zx] lam_xw = lam_wx D^z_x(j) lam_xw literally
    d.at(1, D(x, z, j))
    reroute(d, 1, x, z, w, j)
    # outer: lam_wx D^w_x(j) lam_xw pulls ray x
    d.Q(0, pos(lam(w, x), lam(x, w)), [])
    i = len(D(x, w, j - 1))                             # = 2j - 1
    d.Q(i, pos(lam(w, x), lam(x, w)), [])
    d.at(0, D(x, w, j - 1))
    reroute(d, 0, x, w, c[x], j - 1)
    d.done()                                            # V V^(-1) freely
    assert d.q <= 4, (d.tag, d.q)
    return d


def deriv_B3(c, x, y, i, j):
    """(B) [Ed t_x(i), Ed t_y(j)], x != y, i, j >= 1."""
    z = third(x, y)
    U, V = Ed_t(c, x, i), Ed_t(c, y, j)
    d = Deriv(comm(U, V), 'B3 c=%s x=%d y=%d i=%d j=%d' % (c, x, y, i, j))
    d.normalize()
    q0 = d.q
    lu, lv = len(U), len(V)
    reroute(d, 0, x, c[x], y, i - 1)
    reroute(d, lu, y, c[y], x, j - 1)
    reroute(d, lu + lv, x, c[x], y, i - 1)
    reroute(d, 2 * lu + lv, y, c[y], x, j - 1)
    m = j - 1
    d.conj(pos(*([lam(x, y)] * m)))
    d.normalize()
    Dst = D(x, y, i + j - 2)
    d.at(0, Dst + pos(tau(y)) + Dst + pos(tau(y)))
    n = len(d.w)
    for _ in range(m):                                  # trailing lam_xy^m lam_yx^m
        mid = n - m
        d.Q(mid - 1, pos(lam(x, y), lam(y, x)), [])
        n -= 2
        m -= 1
    # now Dst tau_y Dst tau_y; cyclically this is tau_y Dst tau_y Dst
    d.w = d.w[-1:] + d.w[:-1]                          # cyclic permutation, area-free
    reroute(d, 1, x, y, z, i + j - 2)
    reroute(d, 2 + len(Dst), x, y, z, i + j - 2)
    commute_single(d, pos(tau(y)), D(x, z, i + j - 2))
    d.done()
    assert d.q <= 8 * (i + j), (d.tag, d.q)
    return d


def deriv_C3(c, p, q, z, j):
    """(C) [Ed sigma_{p,q}, Ed t_z(j)], tau-ray p, vertex-disjoint edges."""
    r = third(p, q)
    U, V = Ed_s(p, q), Ed_t(c, z, j)
    d = Deriv(comm(U, V), 'C3 c=%s p=%d q=%d z=%d j=%d' % (c, p, q, z, j))
    d.normalize()
    d.conj(pos(lam(p, q)))
    d.normalize()
    d.Q(0, pos(lam(p, q), lam(q, p)), [])               # lam_pq U -> tau_p lam_pq
    # word: tau_p [lam_pq V lam_qp] tau_p [lam_pq V lam_qp]
    S = pos(lam(p, q)) + V + pos(lam(q, p))
    d.at(0, pos(tau(p)) + S + pos(tau(p)) + S)
    if z == r:
        d.macro(1, S, V, 'D3(%d)' % j)
        d.macro(2 + len(V), S, V, 'D3(%d)' % j)
        reroute(d, 1, r, c[r], q, j - 1)
        reroute(d, 2 + len(V), r, c[r], q, j - 1)
        commute_single(d, pos(tau(p)), D(r, q, j - 1))
    elif z == p:
        assert j >= 2
        reroute(d, 2, p, c[p], q, j - 1)
        reroute(d, len(S) + 3, p, c[p], q, j - 1)
        Dj = D(p, q, j)
        d.at(0, pos(tau(p)) + Dj + pos(tau(p)) + Dj)
        d.macro(0, list(d.w), [], "F'(%d)" % j)
    else:
        assert z == q and j >= 2
        reroute(d, 2, q, c[q], p, j - 1)
        reroute(d, len(S) + 3, q, c[q], p, j - 1)
        for start in (1, None):
            i = 1 if start == 1 else d.find(pos(tau(p)), 1) + 1
            d.Q(i, pos(lam(p, q), lam(q, p)), [])
            e = i + len(D(q, p, j - 2))
            d.Q(e, pos(lam(p, q), lam(q, p)), [])
        Dm = D(q, p, j - 2)
        d.at(0, pos(tau(p)) + Dm + pos(tau(p)) + Dm)
        reroute(d, 1, q, p, r, j - 2)
        reroute(d, 2 + len(Dm), q, p, r, j - 2)
        commute_single(d, pos(tau(p)), D(q, r, j - 2))
    d.done()
    assert d.q <= 12 * j + 8, (d.tag, d.q)
    return d


def route_functions():
    for c1 in (2, 3):
        for c2 in (1, 3):
            for c3 in (1, 2):
                yield {1: c1, 2: c2, 3: c3}


def main(KMAX=12):
    runs = 0
    # N_k represents the pour, for every labeling (Lemma 3 of the pour-doubling note)
    for a, b in itertools.permutations(RAYS, 2):
        cc = third(a, b)
        for k in range(1, KMAX + 1):
            assert equal(pour(a, b, cc, k), pos(*N(a, b, k))), (a, b, k)
            assert all(s in (lam(a, b), lam(b, a), tau(a), tau(b)) for s in N(a, b, k))
    print('N_k = lam_ac^k lam_cb^k, two-ray, all 6 labelings, k <=', KMAX)
    worst = {}
    for x, u in itertools.permutations(RAYS, 2):
        v = third(x, u)
        for k in range(1, KMAX + 1):
            d = deriv_R3(x, u, v, k)
            runs += 1
            worst['R'] = max(worst.get('R', 0), d.q - len(N(u, v, k)) - 4 * k)
        for k in range(2, KMAX + 1):
            deriv_Fprime(x, u, k)
            runs += 1
    print('(R) and (F) derivations: ok')
    for c in route_functions():
        for x in RAYS:
            for k in [0] + list(range(2, KMAX + 1)):     # F_3(1) is not null-homotopic
                deriv_F3(c, x, k)
                runs += 1
            for z, w in itertools.permutations(set(RAYS) - {x}, 2):
                for j in range(1, KMAX + 1):
                    deriv_D3(c, x, z, w, j)
                    runs += 1
        for x, y in itertools.permutations(RAYS, 2):
            for i in range(1, 8):
                for j in range(1, 8):
                    deriv_B3(c, x, y, i, j)
                    runs += 1
        for p, q in itertools.permutations(RAYS, 2):
            for z in RAYS:
                for j in range(1, KMAX + 1):
                    if z in (p, q) and j < 2:
                        continue
                    deriv_C3(c, p, q, z, j)
                    runs += 1
    print('(F3), (D), (B), (C) derivations: ok, all 8 route functions')
    # print one macro multiset per family, as a sample
    c = {1: 2, 2: 3, 3: 1}
    samples = [deriv_R3(1, 2, 3, 5), deriv_Fprime(1, 2, 5), deriv_D3(c, 1, 2, 3, 5),
               deriv_D3(c, 1, 3, 2, 5), deriv_B3(c, 1, 2, 4, 5),
               deriv_C3(c, 1, 2, 3, 5), deriv_C3(c, 1, 2, 1, 5), deriv_C3(c, 1, 2, 2, 5)]
    for d in samples:
        print('   %-32s Q-steps %4d   macros %s' % (d.tag, d.q, ' '.join(d.macros)))
    print('derivations checked:', runs)
    print('ALL OK')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (Fail, AssertionError) as e:
        print('FAIL', e)
        sys.exit(1)
