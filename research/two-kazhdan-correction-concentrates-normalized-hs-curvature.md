---
rg: 2
id: two-kazhdan-correction-concentrates-normalized-hs-curvature
kind: claim
title: Hilbert second-cohomology vanishing concentrates normalized-HS curvature
artifacts:
  - research/artifacts/parallel-arithmetic-holonomy-2026-09-04.md
distinct_from:
  sl3-z-weakly-ucp-stable: that asks for exact correction of every SL_3(Z) approximation; this assumes actual Hilbert H2 vanishing and only concentrates residual curvature, with no assertion for SL_3(Z).
  moving-subgroup-schreier-correction-has-no-index-loss: that consumes exact subgroup holonomy to construct an exact representation; this changes the original tuple and concentrates its curvature but supplies no exact subgroup representation.
---

Let `G=<S|R>` be finitely presented and assume the actual vanishing

```text
H^2(G,H_pi)=0 for every unitary Hilbert representation pi.  (KCC1)
```

This means ordinary cohomology vanishes, not just reduced cohomology.
For any generator tuples `U_j:S->U(d_j)` with positive normalized-HS
defining defect

```text
delta_j=max_(r in R)||U_j(r)-I||_(2,d_j) -> 0,
```

there is a subsequence and tuples `V_j:S->U(d_j)` in the same dimensions
such that

```text
max_s ||V_j(s)-U_j(s)||_2 = O(delta_j),
max_r ||V_j(r)-I||_2 = O(delta_j),
max_r ||V_j(r)-I||_1 = o(delta_j).                         (KCC2)
```

Here `||X||_1=tr_(d_j)|X|` also uses normalized trace. There is no
uniform-integrability hypothesis on the input defects. The assertion is a
subsequence result; its implicit constant is finite along that subsequence.
The same correction gives relator defect `o(delta_j)` in every normalized
Schatten p-norm for `1<=p<2` by interpolation.

In particular there are projections `P_j` with `tr_(d_j)(P_j)->0` such
that, for `Q_j=I-P_j`,

```text
max_(r in R) (||(V_j(r)-I)Q_j||_op
             +||Q_j(V_j(r)-I)||_op) = o(delta_j).         (KCC3)
```

The projections are not claimed invariant under the generators. The HS
defect in `(KCC2)` is still `O(delta_j)`, not `o(delta_j)`, and neither
an exact representation nor exact subgroup holonomy has been obtained.
Deleting `P_j` may introduce boundary errors of order
`sqrt(tr_(d_j)(P_j))`, which need not be `o(delta_j)`.

If the original rescaled relator errors additionally have uniformly
vanishing square tails,

```text
lim_(M->infinity) limsup_j max_r
 ||((U_j(r)-I)/delta_j)
   1_(|(U_j(r)-I)/delta_j|>M)||_2 = 0,
```

then the same argument improves the HS relator defect to `o(delta_j)`.
This tail condition is not asserted to persist when the improved residual
is divided by its new, smaller size, so this subsidiary statement does not
claim that iteration converges to exact representations.

DERIVATION
regular-component-cohomology-concentration-proof
