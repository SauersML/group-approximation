#!/usr/bin/env python3
"""Exact checks for h-mix-halves-are-lef-by-column-windows and
lef-normal-amalgams-need-not-be-mf.

J = F_2<S,T | TS = 1>. An element is a frozenset of monomials (a, b) meaning
S^a T^b (normal-form basis). V_+ = F_2^(N), S e_j = e_{j+1}, T e_j = e_{j-1},
T e_0 = 0. Column space U = V_+ (+) V_+, a matrix B in M_2(J) acts on U by
B_+ (v1, v2) = (B11 v1 + B12 v2, B21 v1 + B22 v2).

Checks (all exact, over F_2):
 1. ring rule and faithfulness sanity for the monomial model;
 2. (E5') ev_Omega(X B) = ev_Omega(X) o B_+|_Omega for Omega = Win_d (+) Win_{d+1}
    and B in {1, b}, b = x_43(S) ~ [[1,0],[S,1]]; and the same for
    Omega = Win_d (+) Win_d and a = x_34(1) ~ [[1,1],[0,1]];
 3. the column model (X, B) -> [[1, ev X], [0, B|Omega]] is multiplicative on
    M x| <b> for random X; head x_13(Q) has nonzero image;
 4. window offsets: Win_d1 (+) Win_d2 is a-invariant iff d2 <= d1 and
    b-invariant iff d2 >= d1 + 1, so no window pair serves D = <a, b>;
 5. c = ab has no nonzero c-invariant subspace inside Win_N (+) Win_N (N <= 14);
 6. doubling identities beta = theta^-1 alpha theta, beta^2 = 1,
    alpha beta = phi^-1 x phi on a toy group.
"""
import itertools
import random

random.seed(20260917)


# ---------- the ring J ----------
def jmul(x, y):
    out = set()
    for (a, b) in x:
        for (c, d) in y:
            m = (a + max(c - b, 0), d + max(b - c, 0))
            out ^= {m}
    return frozenset(out)


def jadd(x, y):
    return frozenset(set(x) ^ set(y))


ZERO = frozenset()
ONE = frozenset({(0, 0)})
S = frozenset({(1, 0)})
T = frozenset({(0, 1)})
Q = jadd(ONE, jmul(S, T))


def jact(x, vec):
    """x in J acting on a vector of V_+ given as a frozenset of indices."""
    out = set()
    for (a, b) in x:
        for s in vec:
            if s >= b:
                out ^= {s - b + a}
    return frozenset(out)


def rand_j(maxdeg=3, terms=3):
    out = set()
    for _ in range(random.randint(0, terms)):
        out ^= {(random.randint(0, maxdeg), random.randint(0, maxdeg))}
    return frozenset(out)


# ---------- 2x2 matrices over J ----------
def mmul(X, Y):
    return tuple(tuple(jadd(jmul(X[i][0], Y[0][j]), jmul(X[i][1], Y[1][j]))
                       for j in range(2)) for i in range(2))


def madd(X, Y):
    return tuple(tuple(jadd(X[i][j], Y[i][j]) for j in range(2)) for i in range(2))


def mact(X, v):
    v1, v2 = v
    return (frozenset(set(jact(X[0][0], v1)) ^ set(jact(X[0][1], v2))),
            frozenset(set(jact(X[1][0], v1)) ^ set(jact(X[1][1], v2))))


I2 = ((ONE, ZERO), (ZERO, ONE))
A_ = ((ONE, ONE), (ZERO, ONE))      # a = x_34(1) on columns
B_ = ((ONE, ZERO), (S, ONE))        # b = x_43(S) on columns
Z2 = ((ZERO, ZERO), (ZERO, ZERO))


def window_basis(d1, d2):
    return [(frozenset({j}), frozenset()) for j in range(d1)] + \
           [(frozenset(), frozenset({j})) for j in range(d2)]


def in_window(v, d1, d2):
    return all(j < d1 for j in v[0]) and all(j < d2 for j in v[1])


def ev(X, basis):
    return [mact(X, w) for w in basis]


def check1():
    assert jmul(T, S) == ONE
    assert jmul(S, T) != ONE
    assert jmul(Q, S) == ZERO and jmul(T, Q) == ZERO
    for a in range(4):
        for c in range(4):
            lhs = jmul(jmul(Q, jmul(frozenset({(0, a)}), frozenset({(c, 0)}))), Q)
            assert lhs == (Q if a == c else ZERO)
    for _ in range(300):
        x, y, z = rand_j(), rand_j(), rand_j()
        assert jmul(jmul(x, y), z) == jmul(x, jmul(y, z))
        v = frozenset(random.sample(range(10), 3))
        assert jact(jmul(x, y), v) == jact(x, jact(y, v))
    print("1 ok: ring rules, associativity, module action")


def check2_3():
    for d in range(1, 8):
        for (B, d1, d2) in ((B_, d, d + 1), (A_, d, d)):
            basis = window_basis(d1, d2)
            for w in basis:
                assert in_window(mact(B, w), d1, d2)
            for _ in range(40):
                X = tuple(tuple(rand_j() for _ in range(2)) for _ in range(2))
                lhs = ev(mmul(X, B), basis)
                rhs = [mact(X, mact(B, w)) for w in basis]
                assert lhs == rhs
        # multiplicativity of the column model on M x| <b>
        basis = window_basis(d, d + 1)
        for _ in range(40):
            X = tuple(tuple(rand_j() for _ in range(2)) for _ in range(2))
            Y = tuple(tuple(rand_j() for _ in range(2)) for _ in range(2))
            for B in (I2, B_):
                for C in (I2, B_):
                    # [[1,X],[0,B]] [[1,Y],[0,C]] = [[1, Y + X C], [0, B C]]
                    prod_X = madd(Y, mmul(X, C))
                    lhs = ev(prod_X, basis)
                    rhs = [(frozenset(set(p[0]) ^ set(q[0])), frozenset(set(p[1]) ^ set(q[1])))
                           for p, q in zip(ev(Y, basis), [mact(X, mact(C, w)) for w in basis])]
                    assert lhs == rhs
        head = ((Q, ZERO), (ZERO, ZERO))
        assert any(v != (frozenset(), frozenset()) for v in ev(head, basis))
    assert mmul(B_, B_) == I2 and mmul(A_, A_) == I2
    print("2,3 ok: (E5') on windows, column model multiplicative on M x| <b>, head kept")


def check4():
    for d1 in range(0, 7):
        for d2 in range(0, 7):
            basis = window_basis(d1, d2)
            a_inv = all(in_window(mact(A_, w), d1, d2) for w in basis)
            b_inv = all(in_window(mact(B_, w), d1, d2) for w in basis)
            assert a_inv == (d2 <= d1), (d1, d2)
            assert b_inv == (d2 >= d1 + 1 or d1 == 0), (d1, d2)
            if d1 >= 1:
                assert not (a_inv and b_inv)
    print("4 ok: window offsets k = d2-d1 need k <= 0 for a and k >= 1 for b")


# ---------- F_2-linear algebra on vectors of U as bitmasks ----------
def to_mask(v, N):
    m = 0
    for j in v[0]:
        m |= 1 << j
    for j in v[1]:
        m |= 1 << (N + j)
    return m


def xreduce(v, basis):
    # basis: list kept sorted by decreasing top bit, distinct top bits
    for bv in basis:
        if v >> (bv.bit_length() - 1) & 1:
            v ^= bv
    return v


def rowreduce(vecs):
    basis = []
    for v in vecs:
        v = xreduce(v, basis)
        if v:
            basis.append(v)
            basis.sort(key=lambda x: -x.bit_length())
    return basis


def largest_invariant_dim(C, N):
    if True:
        width = N + 2  # c raises S-degree by at most 1
        cur = window_basis(N, N)
        while True:
            # U_{k+1} = { v in U_k : c v in U_k }: solve linear system
            cur_masks = rowreduce([to_mask(v, width) for v in cur])
            k = len(cur)
            # images
            imgs = [to_mask(mact(C, v), width) for v in cur]
            # find combinations sum x_i v_i with sum x_i c v_i in span(cur)
            span = cur_masks
            def reduce(m):
                return xreduce(m, span)
            # linear map x -> reduce(sum x_i imgs_i) ; kernel
            red = [reduce(m) for m in imgs]
            # kernel via elimination on augmented vectors
            aug = [(red[i], 1 << i) for i in range(k)]
            kern = []
            piv = []
            for (r, tag) in aug:
                for (pr, ptag) in piv:
                    if r >> (pr.bit_length() - 1) & 1:
                        r, tag = r ^ pr, tag ^ ptag
                if r == 0:
                    kern.append(tag)
                else:
                    piv.append((r, tag))
                    piv.sort(key=lambda x: -x[0].bit_length())
            new = []
            for tag in kern:
                v1, v2 = set(), set()
                for i in range(k):
                    if tag >> i & 1:
                        v1 ^= set(cur[i][0])
                        v2 ^= set(cur[i][1])
                new.append((frozenset(v1), frozenset(v2)))
            new_masks = rowreduce([to_mask(v, width) for v in new])
            if len(new_masks) == len(cur_masks):
                break
            # keep an independent spanning set
            ind = []
            acc = []
            for v in new:
                m = to_mask(v, width)
                t = xreduce(m, acc)
                if t:
                    acc.append(t)
                    acc.sort(key=lambda x: -x.bit_length())
                    ind.append(v)
            cur = ind
            if not cur:
                break
        return len(rowreduce([to_mask(v, width) for v in cur]))


def check5():
    C = mmul(A_, B_)
    for N in range(1, 15):
        assert largest_invariant_dim(C, N) == 0, N
        # positive controls: a and b are involutions; Win_N (+) Win_N is
        # a-invariant, and its largest b-invariant part is Win_{N-1} (+) Win_N
        assert largest_invariant_dim(A_, N) == 2 * N, N
        assert largest_invariant_dim(B_, N) == 2 * N - 1, N
    print("5 ok: no nonzero c-invariant subspace in Win_N (+) Win_N for N <= 14")


def check6():
    n = 7
    phi = lambda x: (3 * x) % n
    phinv = lambda x: (5 * x) % n
    alpha = lambda p: (p[1], p[0])
    beta = lambda p: (phi(p[1]), phinv(p[0]))
    theta = lambda p: (p[0], phi(p[1]))
    thinv = lambda p: (p[0], phinv(p[1]))
    for p in itertools.product(range(n), repeat=2):
        assert beta(beta(p)) == p
        assert beta(p) == thinv(alpha(theta(p)))
        assert alpha(beta(p)) == (phinv(p[0]), phi(p[1]))
    print("6 ok: doubling identities")


if __name__ == "__main__":
    assert len(rowreduce([0b01, 0b11, 0b10])) == 2
    check1()
    check2_3()
    check4()
    check5()
    check6()
    print("ALL OK")
