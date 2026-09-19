---
rg: 2
id: stw99-lxxvi-two-saturated-cell-towers-kill-s6
kind: claim
title: Two-saturated NCCW cell towers kill the unstable scalar S6 class
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let `A_0=directSum_i M_(r_i)` with every `r_i>=2`, and let

```text
A_j=A_(j-1) pullback_(C(S^(k_j-1),F_j)) C(D^(k_j),F_j)
                                                            (1)
```

be a finite unital NCCW cell tower.  At stage `j`, let

```text
partial_j: pi_6(U(M_2(A_(j-1))))
        -> pi_(5+k_j)(U(M_2(F_j)))                         (2)
```

be the connecting map determined by the attaching homomorphism.  If
`image(partial_j)` is 2-saturated at every stage, meaning

```text
2x in image(partial_j)  implies  x in image(partial_j),   (3)
```

then the scalar image of the nonzero
`alpha in pi_5(U(2))=Z/2` vanishes in `pi_5(U(M_2(A_n)))`.

This strictly extends the stable odd-cell criterion.  When `k_j` is odd and
the cell matrices are in stable range, the target in `(2)` is zero.  When
`k_j` is even and the cell matrices are in stable range, the target is a
free lattice `Z^q`; condition `(3)` says exactly that the boundary-image
lattice has no hidden factor of two.  Hence stable even cells are harmless
whenever that lattice is 2-saturated.

In particular, **one arbitrary-dimensional stable cell** attached to a
finite-dimensional zero-skeleton with no scalar summand kills `alpha` for
every attaching map.  For odd cell dimension the target in `(2)` is zero;
for even cell dimension the source
`pi_6(U(M_2(A_0)))` is zero and the cokernel is free abelian.  Thus the first
possible stable even-cell survival mechanism needs at least two cell stages:
an earlier stable odd-dimensional cell must create `pi_6`, and the later
attaching map must embed its boundary image non-2-saturatedly.  Stable even
cells cannot create `pi_6` while it is zero, because their degree-`6+k`
fibre group is stable even and hence zero.

Consequently every stable-cell tower in which no even-dimensional cell
occurs after an odd-dimensional cell kills `alpha` for arbitrary attaching
maps.  The initial even block preserves both scalar vanishing and
`pi_6=0`; the terminal odd block has zero scalar-obstruction target.  Thus a
surviving stable-cell tower must contain an odd-before-even parity inversion
as well as a non-2-saturated boundary image at such an even stage.

More generally, a coefficient algebra for the surviving `S^6` clutching
route can contain no unital copy of a tower satisfying `(3)`.  Any finite
NCCW candidate must exhibit a concrete order-two defect in one of the
attaching-map cokernels; nonzero odd stable homotopy alone is insufficient.
