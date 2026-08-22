---
rg: 2
id: atlas-augmented-rank-zero-set-compactness
kind: claim
title: Promote an augmented Atlas rank-ultraproduct point to a finite matrix zero
distinct_from:
  sublinear-bandwidth-is-vacuous-under-rank-amplification: that removes the apparent band restriction; this is the resulting unrestricted rank-metric compactness problem.
  atlas-block-circulant-joint-escape-promotes-to-exact-mode: fixed-block circulants have residue-field evaluations which prove this promotion in that special commutative class.
  atlas-exact-matrix-zero-set-is-a-finite-quotient-test: that starts with an exact finite matrix zero; this must produce one from an exact point only in a rank ultraproduct.
  growing-rank-decoder-is-linear-soficity: that classifies the ultraproduct point as a linear-sofic representation but supplies no finite-coordinate exactification.
---

OPEN.  Let `E_+` be the finite matrix Laurent system consisting of the
repeated natural-module Atlas packet, collision `19243`, and q14, with its
two faithful marked `A8` charts.  Prove:

```text
there exist m_n -> infinity and T_n in GL_(2m_n)(F2)
with max_(R in E_+) rank R(T_n)/m_n -> 0

                    implies

there exist finite m and T in GL_(2m)(F_(2^f))
with R(T)=0 for every R in E_+.                       (ARC1)
```

Restriction of scalars would make the conclusion an exact binary model, and
the established exact-zero/finite-quotient reduction would then give a
nontrivial finite quotient of the augmented Atlas group.

The hypothesis of `(ARC1)` is exactly an exact faithful-chart point in a
rank-metric matrix ultraproduct.  Coordinatewise direct and stable finiteness
do not prove the conclusion: they preserve one-sided inverse identities in
the ultraproduct but do not lift a general finitely presented algebra
homomorphism to an exact finite-dimensional representation.  Thus `(ARC1)`
is a genuine rank-zero-set compactness/rank-stability statement, not a
consequence of direct finiteness.

By `sublinear-bandwidth-is-vacuous-under-rank-amplification`, adding
`bandwidth(T_n),bandwidth(T_n^-1)=o(m_n)` leaves `(ARC1)` unchanged.  This is
the precise missing theorem for the width-growing noncirculant stitching
lane.

## Attempts

- **Primary Fourier quotients stop at circulants.**  The fixed-block cyclic
  proof has a common central shift and finite residue-field modes.  An
  arbitrary band tuple has no commuting translation algebra, and diagonal
  amplification makes its relative bandwidth vanish without creating one.
- **Stable finiteness is too weak.**  Rank ultraproducts satisfy
  `rank(1-AB)=rank(1-BA)` coordinatewise, but the Atlas system is not a lone
  one-sided-inverse equation.  This identity supplies no exact finite
  coordinate or finite quotient.
- **Finite-section compactness needs uniform propagation.**  A fixed-radius,
  finite-alphabet one-dimensional constraint can be passed to a periodic
  model.  Here the permitted width grows, and amplification realizes every
  unrestricted rank microstate inside that regime.  Invoking such a compactness
  argument would therefore assume `(ARC1)` rather than prove it.
- **The quotient is not itself a graph of finite groups.**
  `atlas-augmented-thirteen-vf-fillings`
  presents it as a virtually free carrier filled by twelve independent cycle
  stable letters and the hyperbolic collision word.  Residual finiteness of
  the carrier does not descend through this multiple filling, and the
  collision misses the available relative small-cancellation threshold.
