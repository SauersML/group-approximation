#!/usr/bin/env python3
"""Sanity checks for baker-lifted-torus-generators-force-diagonal-lamp-shears.

1. Side split of the Proposition B map phi (char-p-burger-lamp-realizations-refute-haagerup,
   Step 7): for (p,k) in {(2,2),(3,4)} compute, by bit flips on random points, the set of
   z-positions each coordinate alpha_m, beta_m depends on, and read off its side
   (x = positions >= 0, y = positions < 0).  Expected: alpha_+ -> y, alpha_- -> x,
   beta_+ -> x, beta_- -> y, so alpha and beta sit on opposite sides at each end.
2. Side rule on generators: A = (gamma^-1)^T; an off-diagonal entry at an end is allowed only
   if both coordinates sit on the same side there.  Lists which generators of EL_2(R) pass.
3. Direct witness for p = 2, k = 2 (phi a homeomorphism): the conjugate of e_12(1) (any
   translation part) changes a deep x-digit when a deep y-digit is flipped, so it does not
   preserve x-tails; every element of 2V does.
"""
import itertools
import random

random.seed(20260917)


def make_phi(p, k):
    words = list(itertools.product([0, 1], repeat=k))
    pairs = [(a, b) for a in range(p) for b in range(p)]
    tau = {w: pairs[i % len(pairs)] for i, w in enumerate(words)}  # surjection
    assert set(tau.values()) == set(pairs)

    def coord(z, eps, m):
        # phi = psi o phi_0 o Theta: alpha_m = first comp of block -m, beta_m = second of block m
        j = -m if eps == 'a' else m
        blk = tuple(z[j * k + i] for i in range(k))
        return tau[blk][0 if eps == 'a' else 1]
    return coord


def dependency(p, k, eps, m, N, trials=40):
    coord = make_phi(p, k)
    dep = set()
    for _ in range(trials):
        z = {i: random.randint(0, 1) for i in range(-N, N)}
        base = coord(z, eps, m)
        for i in range(-N, N):
            z[i] ^= 1
            if coord(z, eps, m) != base:
                dep.add(i)
            z[i] ^= 1
    return dep


def side(dep):
    if not dep:
        return 'none'
    if min(dep) >= 0:
        return 'x'
    if max(dep) < 0:
        return 'y'
    return 'both'


print("== 1. side split of the Proposition B map ==")
ok1 = True
for (p, k) in [(2, 2), (3, 4)]:
    N = 8 * k
    sides = {}
    for eps in 'ab':
        for m in [-5, -4, -3, 3, 4, 5]:
            d = dependency(p, k, eps, m, N)
            sides[(eps, m)] = side(d)
    ends = {}
    for (eps, m), s in sides.items():
        ends.setdefault((eps, '+' if m > 0 else '-'), set()).add(s)
    print(f"(p,k)=({p},{k}) ends:", {e: sorted(v) for e, v in sorted(ends.items())})
    exp = {('a', '+'): {'y'}, ('a', '-'): {'x'}, ('b', '+'): {'x'}, ('b', '-'): {'y'}}
    good = ends == exp
    ok1 &= good
    print("  matches alpha_+:y alpha_-:x beta_+:x beta_-:y ->", good)

print("== 2. side rule on generators (A = (gamma^-1)^T, entries in F_p[t,t^-1]) ==")
S = {('a', '+'): 'y', ('a', '-'): 'x', ('b', '+'): 'x', ('b', '-'): 'y'}


def dual_matrix(g):
    # g = [[a,b],[c,d]] with det 1, entries as dicts exponent->coeff; A = [[d,-c],[-b,a]]
    (a, b), (c, d) = g
    neg = lambda r: {e: -v for e, v in r.items()}
    return [[d, neg(c)], [neg(b), a]]


one, t, zero = {0: 1}, {1: 1}, {}
tinv = {-1: 1}
gens = {
    'e12(1)': [[one, one], [zero, one]], 'e12(t)': [[one, t], [zero, one]],
    'e21(1)': [[one, zero], [one, one]], 'e21(t)': [[one, zero], [t, one]],
    'h=diag(t,1/t)': [[t, zero], [zero, tinv]], 'w': [[zero, one], [{0: -1}, zero]],
}
passes = {}
for name, g in gens.items():
    A = dual_matrix(g)
    allowed = True
    for i, eo in enumerate('ab'):          # output coordinate
        for j, ei in enumerate('ab'):      # input coordinate
            if any(v != 0 for v in A[i][j].values()) and eo != ei:
                for end in '+-':
                    if S[(eo, end)] != S[(ei, end)]:
                        allowed = False
    passes[name] = allowed
    print(f"  {name:14s} liftable by side rule: {allowed}")
ok2 = passes == {'e12(1)': False, 'e12(t)': False, 'e21(1)': False, 'e21(t)': False,
                 'h=diag(t,1/t)': True, 'w': False}

print("== 3. p=2,k=2 witness: conjugated e12(1) couples deep y-digits into deep x-digits ==")
ok3 = True
for v_bit in [0, 1]:
    for m in [4, 7, 11]:
        # z_{2j}=alpha_{-j}, z_{2j+1}=beta_j ; e12(1)+v: beta'_m = beta_m + alpha_m + v_m
        def image_digit(z):
            beta = z[2 * m + 1]
            alpha = z[-2 * m]
            return (beta + alpha + v_bit) % 2  # = z'_{2m+1}, an x-digit at depth 2m+1
        z = {i: random.randint(0, 1) for i in range(-40, 40)}
        before = image_digit(z)
        z[-2 * m] ^= 1  # a y-digit at depth 2m-1
        after = image_digit(z)
        coupled = before != after
        ok3 &= coupled
        print(f"  v={v_bit} m={m}: flipping y-digit at depth {2*m-1} flips x-digit at depth {2*m+1}: {coupled}")

print("ALL OK" if (ok1 and ok2 and ok3) else "FAIL")
