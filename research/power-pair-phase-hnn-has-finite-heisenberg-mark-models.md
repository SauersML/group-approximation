---
rg: 2
id: power-pair-phase-hnn-has-finite-heisenberg-mark-models
kind: claim
title: Coprime power-pair phase HNN cells have exact finite Heisenberg models with live commutator
artifacts:
  - experiments/power_pair_heisenberg_finite_model.py
  - experiments/power_pair_heisenberg_finite_model.json
distinct_from:
  graph-endomorphism-phase-hnn-embeds-formanek-procesi: that proves residual finiteness when one faithful coordinate normalizes the edge map to an ambient graph endomorphism; this gives exact finite marked models even when both faithful power images are proper and the induced partial graph maps do not extend.
  finite-free-phase-product-embedding-has-an-injective-coordinate: that forces one faithful coordinate abstractly; this constructs finite quotients in which both power coordinates are automorphisms and the free commutator remains nontrivial.
  infinite-edge-common-commutant-for-first-chord: that needs a decisive nonamenable return; this rules out commutator collapse for the first explicit nonextendable power-pair candidate.
---

Let `r>=2`, let `m,n>=2`, and consider

```text
E_(m,n)=<F(x_1,...,x_r) times F(y_1,...,y_r),t |
 t x_i t^(-1)=x_i^m y_i^n, 1<=i<=r>.                   (PPH1)
```

For every prime `p` not dividing `mn`, `(PPH1)` has an exact finite
permutation representation in which `[x_1,x_2]` is nontrivial.  Hence no
finite-dimensional soundness theorem for this cell can force the free
commutator mark to collapse, even though both coordinate embeddings
`a_i|->a_i^m` and `a_i|->a_i^n` may have proper image in the free group and
the partial map between them need not extend to an ambient endomorphism.

The construction uses the order-`p^3` Heisenberg group.  It shows that
properness and nonextendability of the infinite edge are not enough: a
decisive HNN return must be **profinitely incompatible** with the marked
packet, meaning that its edge isomorphism cannot descend to marked finite
quotients of this kind.

This does not prove that `E_(m,n)` itself is residually finite or hyperlinear.
It is the exact narrower fence needed here: the candidate has zero-defect
finite models retaining the proposed mark.
