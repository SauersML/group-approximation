"""Independent check of the genus-1 theta certificates in out_small.txt.

For each (C, x, y, z) this verifies, from scratch:
  1. C = <g1, g2> has rank 2, infinite index, and is malnormal (off-diagonal
     components of Gamma_C x Gamma_C are trees);
  2. the theta graph with edges x, y, z from p to q is folded (an immersion);
  3. the boundary word w = x Y z X y Z of its genus-1 ribbon structure is
     cyclically reduced, and w is read as a closed path from some vertex c of
     Gamma_C;
  4. the component of (p, c) in theta x Gamma_C has rank exactly 1.
By Lemmas 2-3 of research/malnormal-free-doubles-surface-certificates-proof.md
this proves that D(F_2, C) = F_2 *_C F_2 contains pi_1(closed genus-2 surface).
"""
from stallings import word, show, fold_subgroup, read, product_component_rank, is_malnormal, infinite_index, rank, INV
from search_genus1 import theta, inv

CERTS = [
    (("abaBa", "AbbAABB"), ("b", "AB", "a")),
    (("bbABBA", "aaBBAAbb"), ("B", "b", "aa")),
    (("aaBBBBA", "AbbabbA"), ("A", "BB", "abb")),
    (("AAAbbb", "AAAbba"), ("B", "a", "Ab")),
]


def main():
    ok_all = True
    for gens, (x, y, z) in CERTS:
        C = fold_subgroup([word(g) for g in gens])
        X, Y_, Z = word(x), word(y), word(z)
        T = theta(X, Y_, Z)
        w = X + inv(Y_) + Z + inv(X) + Y_ + inv(Z)
        cyc_red = all(w[i] != INV(w[(i + 1) % len(w)]) for i in range(len(w)))
        cs = [c for c in range(C.nv()) if read(C, c, w) == c]
        good = [c for c in cs if T is not None and product_component_rank(T, 0, C, c)[0] == 1]
        ok = (rank(C) == 2 and infinite_index(C) and is_malnormal(C) and T is not None
              and cyc_red and bool(good))
        ok_all &= ok
        print("C", gens, "rank", rank(C), "inf-index", infinite_index(C), "malnormal", is_malnormal(C),
              "| theta", x, y, z, "folded", T is not None, "| w", show(w), "cyc-reduced", cyc_red,
              "| closed at", cs, "rank-1 component at", good, "=>", "CERTIFIED" if ok else "FAIL")
    print("all certified:", ok_all)


if __name__ == "__main__":
    main()


def brute_force(maxlen=7):
    """Sanity check independent of fibre products: every reduced word of length
    <= maxlen in the basis u = x Ybar... (u = x inv(y), v = z inv(y)) of pi_1(theta)
    whose value lies in C is a power of w = [u, v] (up to the starting letter)."""
    from itertools import product
    from stallings import reduce_word
    for gens, (x, y, z) in CERTS:
        C = fold_subgroup([word(g) for g in gens])
        u = reduce_word(word(x) + inv(word(y)))
        v = reduce_word(word(z) + inv(word(y)))
        basis = [u, inv(u), v, inv(v)]
        w = reduce_word(u + v + inv(u) + inv(v))
        powers = {tuple(reduce_word(w * k)) for k in range(0, 3)} | {tuple(reduce_word(inv(w) * k)) for k in range(1, 3)}
        bad = hits = 0
        for L in range(1, maxlen + 1):
            for s in product(range(4), repeat=L):
                if any(s[i] == INV(s[i + 1]) for i in range(L - 1)):
                    continue
                g = reduce_word([t for i in s for t in basis[i]])
                if read(C, 0, g) == 0:
                    hits += 1
                    bad += tuple(g) not in powers
        print("brute force", gens, "w", show(w), "elements of A in C not in <w> (A-length <=", maxlen, "):", bad, "| A-words landing in C:", hits)


if __name__ == "__main__":
    brute_force()
