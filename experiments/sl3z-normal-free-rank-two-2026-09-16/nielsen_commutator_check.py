#!/usr/bin/env python3
"""Check Nielsen's commutator theorem on Aut(F_2), with sign = det.

Claim checked (Nielsen 1917/1924): every automorphism alpha of F(a,b) sends
c = [a,b] = a b a^-1 b^-1 to a conjugate of c^eps, where eps = det of the
matrix of alpha on the abelianization Z^2.

The subgroup of Aut(F_2) with this property contains the three elementary
Nielsen transformations (checked below), which generate Aut(F_2) (Nielsen).
The random-product check is only a sanity test of the composition rule.

Words: lists of nonzero ints, 1 = a, 2 = b, negatives = inverses.
Single-threaded, deterministic seed, runs in seconds.
"""
import random

A, B = 1, 2


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def inv(w):
    return [-x for x in reversed(w)]


def cyc_reduce(w):
    w = reduce(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def conjugate_classes_equal(u, v):
    u, v = cyc_reduce(u), cyc_reduce(v)
    if len(u) != len(v):
        return False
    if not u:
        return True
    return any(u[i:] + u[:i] == v for i in range(len(u)))


def apply(alpha, w):
    """alpha: dict {1: word, 2: word} images of a, b."""
    out = []
    for x in w:
        img = alpha[abs(x)]
        out.extend(img if x > 0 else inv(img))
    return reduce(out)


def compose(alpha, beta):
    """(alpha o beta)(x) = alpha(beta(x))."""
    return {1: apply(alpha, beta[1]), 2: apply(alpha, beta[2])}


def abel_matrix(alpha):
    cols = []
    for g in (1, 2):
        w = alpha[g]
        cols.append((sum(1 if x == 1 else -1 if x == -1 else 0 for x in w),
                     sum(1 if x == 2 else -1 if x == -2 else 0 for x in w)))
    return cols  # columns: image of a, image of b


def det(alpha):
    (p, q), (r, s) = abel_matrix(alpha)
    return p * s - q * r


C = [A, B, -A, -B]

SIGMA = {1: [B], 2: [A]}          # swap
IOTA = {1: [-A], 2: [B]}          # invert a
MU = {1: [A, B], 2: [B]}          # a -> ab
GENS = {"sigma": SIGMA, "iota": IOTA, "mu": MU}


def sign_of_commutator(alpha):
    img = apply(alpha, C)
    if conjugate_classes_equal(img, C):
        return +1
    if conjugate_classes_equal(img, inv(C)):
        return -1
    return 0


def main():
    print("c^-1 conjugate to c in F_2:", conjugate_classes_equal(C, inv(C)))
    for name, g in GENS.items():
        print(f"{name}: image of c = {apply(g, C)}, sign = {sign_of_commutator(g)},"
              f" det = {det(g)}")
        assert sign_of_commutator(g) == det(g)
    rng = random.Random(20260916)
    gens = list(GENS.values())
    bad = 0
    for trial in range(3000):
        alpha = {1: [A], 2: [B]}
        for _ in range(rng.randint(1, 25)):
            alpha = compose(alpha, rng.choice(gens))
        s = sign_of_commutator(alpha)
        if s == 0 or s != det(alpha):
            bad += 1
    print("random products checked: 3000, failures:", bad)
    assert bad == 0
    print("OK")


if __name__ == "__main__":
    main()
