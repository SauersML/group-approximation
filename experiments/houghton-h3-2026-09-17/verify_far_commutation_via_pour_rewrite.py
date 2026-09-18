#!/usr/bin/env python3
"""Check the element identities and word bookkeeping behind
  Area_H3(w_k) <= 4 A_3(k-2) + 2k^3 + 14k   (k >= 3)
in research/artifacts/zp-houghton-h3-far-commutation-via-pour-rewrite-2026-09-18.md.

Conventions as in research/artifacts/zp-houghton-pours-2026-09-17.md, Section 0:
points (x,p), p >= 1; right action; words read left to right.
  lam(x,y): (x,p)->(x,p-1) for p>=2, (x,1)->(y,1), (y,p)->(y,p+1).
  tau(x): swaps (x,1),(x,2).
A word is a list of letters ('lam',x,y,e) / ('tau',x,e), e = +1 or -1 (formal inverse).

For all 6 labelings (a,b,c) of the rays {0,1,2} of H_3 and small k, j it checks:
 (0) w_k = [tau_a, D^b_a(k)] is trivial, D^b_a(k) = ((a,k+1),(a,k+2));
 (1) tau_a = lam_ab^2 tau_b lam_ba^2 as elements;
 (2) conjugating w_k by lam_ab^k and substituting tau_a -> lam_ab^2 tau_b lam_ba^2
     inside T = lam_ab^-k tau_a lam_ab^k gives, freely (lam_yx = lam_xy^-1,
     tau^-1 = tau), a cyclic conjugate of [D^a_b(k-2), tau_a];
 (3) D^a_b(j) = D^c_b(j) as elements; letters of D^c_b(j) avoid ray a;
 (4) D^a_b(j) D^c_b(j)^-1 is freely a cyclic conjugate of tau_b V tau_b V^-1 with
     V = E^b_(a,c)(j) = lam_ab^j lam_bc^j;
 (5) V = N_(a,c)(j) = lam_ac^j rho_c(j) as elements, |N| <= j^3, and every letter of N
     has ray support in {a,c} (so commutes letterwise with tau_b).
"""
import itertools
import sys


def L(x, y, e=1):
    return ('lam', x, y, e)


def T(x, e=1):
    return ('tau', x, e)


def act(letter, pt):
    r, p = pt
    if letter[0] == 'tau':
        x = letter[1]
        return (x, 3 - p) if r == x and p in (1, 2) else pt
    _, x, y, e = letter
    if e == -1:
        x, y = y, x
    if r == x:
        return (x, p - 1) if p >= 2 else (y, 1)
    if r == y:
        return (y, p + 1)
    return pt


def apply(word, pt):
    for l in word:
        pt = act(l, pt)
    return pt


def inv(word):
    out = []
    for l in reversed(word):
        out.append(l[:-1] + (-l[-1],))
    return out


def free_key(l):
    # map a letter to (generator, exponent) in the free group used for "freely"
    if l[0] == 'tau':
        return (('t', l[1]), 1)  # tau^-1 = tau: treat as an involution below
    _, x, y, e = l
    if x < y:
        return (('g', x, y), e)
    return (('g', y, x), -e)


def free_reduce(word):
    st = []
    for l in word:
        g, e = free_key(l)
        if st and st[-1][0] == g and (g[0] == 't' or st[-1][1] == -e):
            st.pop()
        else:
            st.append((g, e))
    return st


def cyclic_reduce(st):
    st = list(st)
    while len(st) >= 2 and st[0][0] == st[-1][0] and (st[0][0][0] == 't' or st[0][1] == -st[-1][1]):
        st = st[1:-1]
    return st


def cyc_equal(u, v):
    a, b = cyclic_reduce(free_reduce(u)), cyclic_reduce(free_reduce(v))
    if len(a) != len(b):
        return False
    if not a:
        return True
    return any(a[i:] + a[:i] == b for i in range(len(a)))


def D(a, b, k):  # D^b_a(k) = lam_ab^k tau_a lam_ba^k
    return [L(a, b)] * k + [T(a)] + [L(b, a)] * k


def E(x, y, z, m):  # E^z_(x,y)(m) = lam_xz^m lam_zy^m
    return [L(x, z)] * m + [L(z, y)] * m


def N(x, y, m):  # lam_xy^m rho_y(m), s_i = lam_yx^(i-1) tau_y lam_xy^(i-1)
    w = [L(x, y)] * m
    for i in range(m - 1, 0, -1):
        for jj in range(1, i + 1):
            w += [L(y, x)] * (jj - 1) + [T(y)] + [L(x, y)] * (jj - 1)
    return w


def same_elt(u, v, rays=range(3)):
    depth = max(len(u), len(v)) + 3
    return all(apply(u, (r, p)) == apply(v, (r, p)) for r in rays for p in range(1, depth + 1))


def comm(u, v):
    return u + v + inv(u) + inv(v)


def main(K=9):
    cases = 0
    for a, b, c in itertools.permutations(range(3)):
        assert same_elt([T(a)], [L(a, b)] * 2 + [T(b)] + [L(b, a)] * 2)            # (1)
        for k in range(3, K + 1):
            Dk = D(a, b, k)
            assert all(apply(Dk, (a, p)) == (a, {k + 1: k + 2, k + 2: k + 1}.get(p, p))
                       for p in range(1, 3 * k))                                   # (0)
            wk = comm([T(a)], Dk)
            assert same_elt(wk, [])
            h = [L(a, b)] * k
            conj = inv(h) + wk + h
            sub = [L(a, b)] * 2 + [T(b)] + [L(b, a)] * 2
            Tk = inv(h) + sub + h                                                   # T after substitution
            target = comm(D(b, a, k - 2), [T(a)])
            # (2): conj -> T tau_a T^-1 tau_a^-1 freely, then T -> substituted T
            assert cyc_equal(conj, comm(inv(h) + [T(a)] + h, [T(a)]))
            assert cyc_equal(comm(Tk, [T(a)]), target)
            cases += 1
        for j in range(0, K + 1):
            Da, Dc = D(b, a, j), D(b, c, j)
            assert same_elt(Da, Dc)                                                 # (3)
            assert all(a not in l[1:-1] for l in Dc)
            V = E(a, c, b, j)
            assert cyc_equal(Da + inv(Dc), [T(b)] + V + [T(b)] + inv(V))            # (4)
            if j >= 1:
                Nw = N(a, c, j)
                assert same_elt(V, Nw)                                              # (5)
                assert len(Nw) <= j ** 3
                assert all(set(l[1:-1]) <= {a, c} for l in Nw)
            cases += 1
    print(f"checked {cases} cases (6 labelings of the rays of H_3, 3<=k<={K}, 0<=j<={K}): "
          f"w_k ~ [D^a_b(k-2), tau_a]; D^a_b(j)=D^c_b(j); D^a_b D^c_b^-1 ~ [tau_b, E^b_(a,c)]; "
          f"E^b_(a,c)(j) = N_(a,c)(j) with letters in rays {{a,c}}")


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 9)
