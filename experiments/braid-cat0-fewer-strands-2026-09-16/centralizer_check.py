#!/usr/bin/env python3
"""Sanity check for Proposition B of
research/artifacts/braid-cat0-fewer-strands-2026-09-16.md:

    C_{B_{n+1}}(iota(Delta^2_n)) = iota(B_n) x <Delta^2_{n+1}>.

Method (independent of the proof in the artifact):
- braids are represented faithfully by the Artin action on the free group
  F_{n+1} = <x_1, ..., x_{n+1}> (sigma_i: x_i -> x_i x_{i+1} x_i^-1,
  x_{i+1} -> x_i), elements are hashed by the tuple of reduced images;
- a breadth-first search lists all elements of B_{n+1} of word length <= L;
- for each one commuting with gamma = (sigma_1 ... sigma_{n-1})^n
  (= iota(Delta^2_n)), check that it equals z^k v with z = Delta^2_{n+1}
  = (sigma_1 ... sigma_n)^{n+1}, |k| <= K, and v in the ball of radius L2 of
  B_n = <sigma_1, ..., sigma_{n-1}>;
- also check that each such element fixes the last strand, and that
  z^k lies in iota(B_n) only for k = 0 (within the ball), as a direct-product
  check.

Usage: python3 centralizer_check.py n L L2 K
"""
import sys
from collections import deque


def reduce_word(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def inv_word(w):
    return tuple(-a for a in reversed(w))


def gen_images(m, s):
    """Images of x_1..x_m under the Artin automorphism of generator s (+-i)."""
    i = abs(s)
    imgs = [(j,) for j in range(1, m + 1)]
    if s > 0:
        imgs[i - 1] = (i, i + 1, -i)
        imgs[i] = (i,)
    else:
        imgs[i - 1] = (i + 1,)
        imgs[i] = (-(i + 1), i, i + 1)
    return tuple(imgs)


def substitute(word, phi):
    out = []
    for a in word:
        img = phi[abs(a) - 1]
        out.extend(img if a > 0 else inv_word(img))
    return reduce_word(out)


def compose(phi, psi):
    """(phi o psi)(x_j) = phi(psi(x_j)); multiplicative in word order."""
    return tuple(substitute(psi[j], phi) for j in range(len(psi)))


def identity(m):
    return tuple((j,) for j in range(1, m + 1))


def word_to_aut(m, word):
    phi = identity(m)
    for s in word:
        phi = compose(phi, gen_images(m, s))
    return phi


def ball(m, gens, radius):
    """All elements of <gens> in B_m of word length <= radius, as automorphisms."""
    start = identity(m)
    seen = {start: ()}
    frontier = [start]
    for _ in range(radius):
        nxt = []
        for phi in frontier:
            w = seen[phi]
            for s in gens:
                if w and w[-1] == -s:
                    continue
                psi = compose(phi, gen_images(m, s))
                if psi not in seen:
                    seen[psi] = w + (s,)
                    nxt.append(psi)
        frontier = nxt
    return seen


def permutation(m, word):
    perm = list(range(m + 1))  # position -> strand label, 1-based
    for s in word:
        i = abs(s)
        perm[i], perm[i + 1] = perm[i + 1], perm[i]
    return perm


def main():
    n, L, L2, K = (int(a) for a in sys.argv[1:5])
    m = n + 1
    gens_big = [s for i in range(1, m) for s in (i, -i)]
    gens_small = [s for i in range(1, n) for s in (i, -i)]
    gamma_w = tuple(list(range(1, n)) * n)
    z_w = tuple(list(range(1, m)) * m)
    zinv_w = inv_word(z_w)
    gamma = word_to_aut(m, gamma_w)
    z = word_to_aut(m, z_w)
    zinv = word_to_aut(m, zinv_w)

    # table of z^k v
    small = ball(m, gens_small, L2)
    table = {}
    zk = {0: identity(m)}
    for k in range(1, K + 1):
        zk[k] = compose(zk[k - 1], z)
        zk[-k] = compose(zk[-(k - 1)], zinv)
    for k in range(-K, K + 1):
        for v in small:
            table.setdefault(compose(zk[k], v), (k, small[v]))

    # direct-product check within the ball
    for k in range(-K, K + 1):
        if k != 0 and zk[k] in small:
            print("DIRECT PRODUCT FAILURE: z^%d in iota(B_n) ball" % k)

    big = ball(m, gens_big, L)
    n_comm = 0
    n_found = 0
    n_last_fixed = 0
    missing = []
    for phi, w in big.items():
        if compose(phi, gamma) != compose(gamma, phi):
            continue
        n_comm += 1
        perm = permutation(m, w)
        if perm[m] == m:
            n_last_fixed += 1
        if phi in table:
            n_found += 1
        else:
            missing.append(w)
    print("n=%d: |ball_%d(B_%d)| = %d, |table| = %d" % (n, L, m, len(big), len(table)))
    print("  commuting with gamma: %d, last strand fixed: %d, in <z> iota(B_n): %d"
          % (n_comm, n_last_fixed, n_found))
    for w in missing[:10]:
        print("  NOT FOUND (increase L2/K?):", w)
    # z and gamma commute, delta = gamma^-1 z commutes with gamma
    delta = compose(word_to_aut(m, inv_word(gamma_w)), z)
    print("  delta commutes with gamma:", compose(delta, gamma) == compose(gamma, delta))
    print("  delta in <z> iota(B_n) table:", delta in table, table.get(delta))


if __name__ == "__main__":
    main()
