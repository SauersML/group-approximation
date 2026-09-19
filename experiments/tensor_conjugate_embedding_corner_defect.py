"""Exact checks for the u (x) u (x) conj(u) corner-reconstruction defect.

Replays the calculations of
`unitary-embedding-does-not-preserve-corner-orthogonality`:

  (TCE1) Phi(u)=u (x) u (x) conj(u) is multiplicative, unital and fixes
         every scalar unitary;
  (TCE2) its eigenvalue list on the diagonal torus contains each lambda_i,
         so Phi is injective on U(3);
  (TCE3) the induced projection map F(p)=(I-Phi(I-2p))/2 has
         rank F(p)=rank F(q)=13, rank F(p)F(q)=6, rank F(p+q)=14 for
         orthogonal rank-one p,q in M_3, so orthogonality and additivity
         both fail, with additive error 2 F(p)F(q);
  (TCE4) the three-hot atom of a normalized-rank table has exact
         normalized rank 6 a_i a_j a_k, and the total three-hot mass is
         1 - 3 sum a_i^2 + 2 sum a_i^3.

Exact integer and rational arithmetic; no external packages.  It verifies
a finite tensor model, not any group-level MF statement.
"""

from fractions import Fraction as F
from itertools import product

LABELS = (0, 1, 2)
TRIPLES = list(product(LABELS, repeat=3))


def reflection_signs(support):
    """Diagonal signs of Phi(I-2p) for p the projection onto `support`."""
    signs = {}
    for triple in TRIPLES:
        parity = sum(1 for label in triple if label in support) % 2
        signs[triple] = -1 if parity else 1
    return signs


def projection(support):
    """Diagonal entries of F(p)=(I-Phi(I-2p))/2, a 0/1 vector on 27 atoms."""
    signs = reflection_signs(support)
    return {triple: (1 - signs[triple]) // 2 for triple in TRIPLES}


def rank(vector):
    return sum(vector.values())


def check_homomorphism_and_scalars():
    """(TCE1)-(TCE2) on the diagonal torus, with exact fourth roots."""
    roots = [complex(1, 0), complex(0, 1), complex(-1, 0), complex(0, -1)]

    def phi_eigenvalues(diag):
        return [diag[i] * diag[j] * diag[k].conjugate()
                for (i, j, k) in TRIPLES]

    for z in roots:                                  # Phi(zI) = zI
        assert phi_eigenvalues([z, z, z]) == [z] * 27
    for u in product(roots, repeat=3):               # multiplicativity
        for v in product(roots, repeat=3):
            product_diag = [a * b for a, b in zip(u, v)]
            assert phi_eigenvalues(product_diag) == [
                a * b for a, b in zip(phi_eigenvalues(list(u)),
                                      phi_eigenvalues(list(v)))]
        # each lambda_i occurs, at (i,j,j), so Phi(u)=I forces u=I
        for i in LABELS:
            assert u[i] in phi_eigenvalues(list(u))
        if phi_eigenvalues(list(u)) == [complex(1, 0)] * 27:
            assert list(u) == [complex(1, 0)] * 3


def check_orthogonality_and_additivity():
    """(TCE3): the 27-dimensional counterexample, by exhaustive count."""
    fp, fq = projection({0}), projection({1})
    fpq = projection({0, 1})
    meet = {t: fp[t] * fq[t] for t in TRIPLES}
    assert rank(fp) == 13 and rank(fq) == 13
    assert rank(meet) == 6
    assert sorted(t for t in TRIPLES if meet[t]) == sorted(
        t for t in TRIPLES if sorted(t) == [0, 1, 2])
    assert rank(fpq) == 14
    # F(p+q) = F(p) + F(q) - 2 F(p) F(q), so the additive error is 2F(p)F(q).
    for t in TRIPLES:
        assert fpq[t] == fp[t] + fq[t] - 2 * meet[t]
    assert F(rank(meet), 27) == F(2, 9)
    assert F(2 * rank(meet), 27) == F(4, 9)
    # F(1-p) = 1 - F(p): complement preservation holds and does not help.
    complement = projection({1, 2})
    for t in TRIPLES:
        assert complement[t] == 1 - fp[t]


def three_hot_mass(weights):
    """Exact normalized rank of the three-hot sector for a rank table."""
    n = len(weights)
    total = F(0)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                atom = 6 * weights[i] * weights[j] * weights[k]
                total += atom
    return total


def check_three_hot_formula():
    """(TCE4): 6 sum_{i<j<k} a_i a_j a_k = 1 - 3 sum a^2 + 2 sum a^3."""
    tables = [
        [F(1, 3)] * 3,
        [F(1, 2), F(1, 4), F(1, 4)],
        [F(13, 27), F(8, 27), F(6, 27)],
        [F(1, 5), F(1, 5), F(1, 5), F(1, 5), F(1, 5)],
        [F(1, 2), F(1, 6), F(1, 6), F(1, 6)],
    ]
    for weights in tables:
        assert sum(weights) == 1
        closed = (1 - 3 * sum(a * a for a in weights)
                  + 2 * sum(a * a * a for a in weights))
        assert three_hot_mass(weights) == closed
    # The 27-dimensional example is the uniform rank-one table.
    assert three_hot_mass([F(1, 3)] * 3) == F(6, 27) == F(2, 9)


def main():
    check_homomorphism_and_scalars()
    check_orthogonality_and_additivity()
    check_three_hot_formula()
    fp, fq = projection({0}), projection({1})
    meet = {t: fp[t] * fq[t] for t in TRIPLES}
    print('ranks F(p), F(q), F(p)F(q), F(p+q) =',
          rank(fp), rank(fq), rank(meet), rank(projection({0, 1})))
    print('normalized three-hot mass of the uniform table =',
          three_hot_mass([F(1, 3)] * 3))
    print('All exact arithmetic checks passed.')


if __name__ == '__main__':
    main()
