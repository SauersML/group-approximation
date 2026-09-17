#!/usr/bin/env python3
"""End-to-end check of the doubly-exponential period growth in the bit-register cloning group.

Part 1  phi: the configuration action of triples (T_-, sigma, T_+) is invariant under
        expansion and multiplicative on triples with matching middle tree.
Part 2  placement maps: f_{ijk} = B_j^{k-j-1} B_i^{j-i-1} A^{i-1} sends (p_1,p_2,p_3) to
        (p_i,p_j,p_k), p_t = 1 - 2^-t, computed with the actual PL maps A, B_1.
Part 3  counter circuit: the reversible circuit C_s realises P = Inc_v o T_a on the
        ancilla-zero subspace, ord(P) >= lcm(1..2^s-1), and the word w_s has
        length <= 31 s^3 (explicit count printed).
"""
import itertools
import math
import random
from fractions import Fraction as Fr

from check_cloning_axioms import kappa, rand_perm, compose, bits

random.seed(7)

# ---------------------------------------------------------------- trees and PL maps
def split(leaves, k):  # add caret to leaf k (1-based)
    a, b = leaves[k - 1]
    m = (a + b) / 2
    return leaves[:k - 1] + [(a, m), (m, b)] + leaves[k:]


def rand_tree(n):
    leaves = [(Fr(0), Fr(1))]
    while len(leaves) < n:
        leaves = split(leaves, random.randrange(1, len(leaves) + 1))
    return leaves


def pl(dom, cod):
    """PL map sending the leaves of dom affinely onto the leaves of cod."""
    def f(x):
        for (a, b), (c, d) in zip(dom, cod):
            if a <= x < b or (x == 1 and b == 1):
                return c + (x - a) * (d - c) / (b - a)
        raise ValueError(x)
    return f


def phi(tm, s, tp):
    """Configuration action of (T_-, s, T_+): c -> c' (configurations are functions D_0 -> {0,1})."""
    f_inv = pl(tm, tp)
    left_m = [a for a, _ in tm]
    left_p = [a for a, _ in tp]

    def act(c):
        def c2(q):
            if q in left_m:
                vec = s[tuple(c(a) for a in left_p)]
                return vec[left_m.index(q)]
            return c(f_inv(q))
        return c2
    return act


def rand_config():
    salt = random.random()
    return lambda p: hash((p, salt)) & 1


def rand_dyadic(D=12):
    return Fr(random.randrange(2 ** D), 2 ** D)


def check_phi(trials=40):
    for _ in range(trials):
        n = random.randrange(1, 4)
        tm, tp, s = rand_tree(n), rand_tree(n), rand_perm(n)
        k = random.randrange(1, n + 1)
        e = phi(split(tm, k), kappa(s, n, k), split(tp, k))
        o = phi(tm, s, tp)
        c = rand_config()
        qs = [rand_dyadic() for _ in range(60)] + [a for a, _ in split(tm, k)]
        assert all(e(c)(q) == o(c)(q) for q in qs), "expansion invariance"
        # multiplicativity (T,g,S)(S,h,U) = (T,gh,U)
        S, U, g, h = tp, rand_tree(n), rand_perm(n), rand_perm(n)
        lhs = phi(tm, g, S)(phi(S, h, U)(c))
        rhs = phi(tm, compose(g, h), U)(c)
        assert all(lhs(q) == rhs(q) for q in qs), "multiplicativity"
    print("phi: expansion invariance and multiplicativity OK on", trials, "random cases")


# ---------------------------------------------------------------- placement maps in F
H = Fr(1, 2)
A = pl([(0, Fr(1, 4)), (Fr(1, 4), H), (H, 1)], [(0, H), (H, Fr(3, 4)), (Fr(3, 4), 1)])
A_inv = pl([(0, H), (H, Fr(3, 4)), (Fr(3, 4), 1)], [(0, Fr(1, 4)), (Fr(1, 4), H), (H, 1)])
B1 = pl([(0, H), (H, Fr(5, 8)), (Fr(5, 8), Fr(3, 4)), (Fr(3, 4), 1)],
        [(0, H), (H, Fr(3, 4)), (Fr(3, 4), Fr(7, 8)), (Fr(7, 8), 1)])


def p(t):
    return 1 - Fr(1, 2 ** t)


def placement_word(i, j, k):
    """Word for f_ijk (list of letters, rightmost applied first); 'A', 'a' = A^-1, 'B' = B_1."""
    def Bpow(m, r):  # B_m^r = A^(m-1) B_1^r A^-(m-1)
        return ['A'] * (m - 1) + ['B'] * r + ['a'] * (m - 1) if r > 0 else []
    return Bpow(j, k - j - 1) + Bpow(i, j - i - 1) + ['A'] * (i - 1)


def evaluate(word, x):
    for letter in reversed(word):
        x = {'A': A, 'a': A_inv, 'B': B1}[letter](x)
    return x


def check_placement(wmax=14):
    for i, j, k in itertools.combinations(range(1, wmax + 1), 3):
        wd = placement_word(i, j, k)
        assert [evaluate(wd, p(t)) for t in (1, 2, 3)] == [p(i), p(j), p(k)]
        assert len(wd) <= 5 * k
    print("placement maps f_ijk verified for all i<j<k <=", wmax)


# ---------------------------------------------------------------- counter circuit
def circuit(s):
    w = 3 * s
    a = list(range(1, s + 1))
    v = list(range(s + 1, 2 * s + 1))
    z = list(range(2 * s + 1, 3 * s - 1))
    f1, f2 = 3 * s - 1, 3 * s

    def pad(used):
        extra = [q for q in range(1, w + 1) if q not in used]
        return tuple(used) + tuple(extra[:3 - len(used)])

    def tof(c1, p1, c2, p2, t):
        return (lambda x: (x[0], x[1], x[2] ^ int(x[0] == p1 and x[1] == p2)), (c1, c2, t))

    def cnot(c, pc, t):
        return (lambda x: (x[0], x[1] ^ int(x[0] == pc), x[2]), pad([c, t]))

    def neg(t):
        return (lambda x: (1 - x[0], x[1], x[2]), pad([t]))

    def mcx(ctrls, t):
        k = len(ctrls)
        if k == 0:
            return [neg(t)]
        if k == 1:
            return [cnot(ctrls[0][0], ctrls[0][1], t)]
        if k == 2:
            return [tof(ctrls[0][0], ctrls[0][1], ctrls[1][0], ctrls[1][1], t)]
        comp = [tof(ctrls[0][0], ctrls[0][1], ctrls[1][0], ctrls[1][1], z[0])]
        for i in range(2, k - 1):  # z_i ^= z_{i-1} and c_{i+1}
            comp.append(tof(z[i - 2], 1, ctrls[i][0], ctrls[i][1], z[i - 1]))
        mid = tof(z[k - 3], 1, ctrls[k - 1][0], ctrls[k - 1][1], t)
        return comp + [mid] + comp[::-1]

    def eq_a(t):
        xs = [cnot(a[i], 1, v[i]) for i in range(s)]
        return xs + mcx([(q, 0) for q in v], t) + xs

    def eq_1(t):
        return mcx([(q, 1) for q in v], t)

    gates = eq_a(f1) + eq_1(f2)
    gates += [tof(f1, 1, a[i], 0, v[i]) for i in range(s)]
    gates += [tof(f2, 1, a[i], 0, v[i]) for i in range(s)]
    gates += eq_1(f1) + eq_a(f2)
    for j in range(s, 0, -1):  # increment v (v_1 least significant)
        gates += mcx([(v[i], 1) for i in range(j - 1)], v[j - 1])
    return w, gates


def run_via_group(s, state, gates):
    """Apply w_s = product of f g f^-1; gate positions come from the actual PL maps."""
    index = {p(t): t for t in range(1, 3 * s + 1)}
    for fn, wires in gates:
        order = sorted(wires)
        wd = placement_word(*order)
        pos = [index[evaluate(wd, p(t))] for t in (1, 2, 3)]
        assert pos == order
        x = fn(tuple(state[q] for q in wires))
        for q, bit in zip(wires, x):
            state[q] = bit
    return state


def check_counter(smax=5):
    for s in range(2, smax + 1):
        w, gates = circuit(s)
        N = len(gates)
        L = sum(2 * len(placement_word(*sorted(wires))) + 1 for _, wires in gates)
        perm = {}
        for aval in range(2 ** s):
            for vval in range(2 ** s):
                st = [0] * (w + 1)
                for i in range(s):
                    st[1 + i] = (aval >> i) & 1
                    st[s + 1 + i] = (vval >> i) & 1
                st = run_via_group(s, st, gates)
                assert all(b == 0 for b in st[2 * s + 1:]), "ancillas not restored"
                assert [st[1 + i] for i in range(s)] == [(aval >> i) & 1 for i in range(s)]
                vout = sum(st[s + 1 + i] << i for i in range(s))
                top = 2 ** s - 1
                tv = top if vval == aval else (aval if vval == top else vval)
                assert vout == (tv + 1) % 2 ** s, "P mismatch"
                perm[(aval, vval)] = (aval, vout)
        order, seen = 1, set()
        for x in perm:
            if x in seen:
                continue
            n, y = 0, x
            while y not in seen:
                seen.add(y)
                y = perm[y]
                n += 1
            order = math.lcm(order, n)
        target = math.lcm(*range(1, 2 ** s))
        assert order % target == 0
        assert N <= s * s + 14 * s and L <= 248 * s ** 3
        print(f"s={s}: wires={w} gates={N} word length={L} (<=248 s^3={248*s**3}) "
              f"ord(P)={order} lcm(1..2^s-1)={target}")


if __name__ == "__main__":
    check_phi()
    check_placement()
    check_counter()
