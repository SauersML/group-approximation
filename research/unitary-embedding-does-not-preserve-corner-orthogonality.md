---
rg: 2
id: unitary-embedding-does-not-preserve-corner-orthogonality
kind: claim
title: A scalar-preserving unitary group embedding need not preserve corner orthogonality
invalidates:
  - atomic-return-via-unitary-group-corner-recovery
artifacts:
  - experiments/tensor_conjugate_embedding_corner_defect.py
  - research/artifacts/non-mf-without-property-t.md
distinct_from:
  odd-tensor-closure-forces-a-threehot-hidden-sector: that is a statement about the visible joint spectrum of marked representations, closed under the ternary sum by the tensor cube, with a lower bound on the leaked three-hot trace mass; this is a statement about one fixed embedding, namely that the projection map it induces destroys orthogonality and additivity, and it supplies the exact three-hot rank rather than a bound.
  binary-leavitt-atomic-morita-return: that is the open decoder asking for four coefficient operators on a prescribed marked corner; this refutes one prospective supplier of that decoder, and leaves every other route into it untouched.
  properly-infinite-cstar-quotient-is-compatible-with-fp-mf-group: that shows a properly infinite unitary-generated C-star quotient of an MF group exists, so the one-sided inverse alone obstructs nothing; this shows that even a faithful scalar-preserving embedding of the unitary group fails to transport the projection lattice that such a quotient would have to supply.
  finite-vn-toeplitz-coefficient-reconstruction-fails: that obstructs reconstructing Toeplitz coefficients inside a finite von Neumann algebra by an index or trace argument; this is an exact 27-dimensional counterexample to the order-theoretic step, and its map is injective, unital and scalar preserving.
---

**ESTABLISHED FINITE COUNTEREXAMPLE.**  Let `E=C^3`, let `bar(E)` be its
conjugate Hilbert space, and define

```text
Phi:U(E)->U(E tensor E tensor bar(E)),
Phi(u)=u tensor u tensor bar(u).                        (TCE1)
```

`Phi` is an injective group homomorphism and `Phi(zI)=zI` for every
`|z|=1`.  Nevertheless the induced map on projections

```text
F(p)=(I-Phi(I-2p))/2                                    (TCE2)
```

preserves neither orthogonality nor addition of orthogonal projections.
For `p=diag(1,0,0)` and `q=diag(0,1,0)`, so that `pq=0`,

```text
rank F(p)=rank F(q)=13,
rank F(p)F(q)=6,          tr_27(F(p)F(q))=2/9,
||F(p)F(q)||=1,                                         (TCE3)
```

while `r_(p+q)=r_p r_q` gives

```text
F(p+q)=F(p)+F(q)-2F(p)F(q),      rank F(p+q)=14,        (TCE4)
```

so the additive error has operator norm `2` and normalized trace `4/9`.

There is no missing scalar relation to add.  All scalar unitaries are
preserved, as are all group relations, inverses, conjugations and
commutations, and scalar preservation additionally gives `F(1-p)=1-F(p)`.
Complement preservation and commutation still do not supply orthogonality
or order preservation.

The same computation gives the exact leaked mass, not just a bound.  If a
representation contains pairwise orthogonal projections `P_1,...,P_m` of
normalized ranks `alpha_1,...,alpha_m` summing to `I`, then in
`u -> u tensor u tensor bar(u)` the three-hot atom on distinct `i,j,k` has
normalized rank exactly

```text
6 alpha_i alpha_j alpha_k,                              (TCE5)
```

its range being the orthogonal sum of the six permuted tensor products, and
the total three-hot mass is

```text
6 sum_(i<j<k) alpha_i alpha_j alpha_k
 =1-3 sum_i alpha_i^2+2 sum_i alpha_i^3.                (TCE6)
```

## Consequence

This rules out the proposed general implication from a raw unitary group
embedding to corner reconstruction: a route which starts in a properly
infinite algebra, where isometries have a genuine one-to-two range
decomposition, and then recovers that decomposition from the algebra's
abstract unitary group inside finite matrices, has no order-theoretic step
to stand on.  It does not rule out a finite-coordinate decoder with
additional proved hypotheses, and it is not a model of the full Leavitt
candidate.
