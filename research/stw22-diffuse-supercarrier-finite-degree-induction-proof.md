---
rg: 2
id: stw22-diffuse-supercarrier-finite-degree-induction-proof
kind: route
title: Induct the Grassmannian, carrier, and stabilizer Michael indices in lockstep
target: stw22-diffuse-stiefel-all-finite-sphere-fillings
requires:
  - stw22-diffuse-stiefel-uniform-loop-fillings
  - stw22-diffuse-stiefel-uniform-four-sphere-fillings
artifacts:
  - research/artifacts/stw22-diffuse-all-degree-induction-audit-2026-08-31.md
---

Let `S_d` denote the assertion that all diffuse Stiefel spaces are
`d`-connected, form a factor-uniform equi-`LC^d` family, and have the
top-degree small-sphere modulus (AD-1). The established path and loop
theorems give `S_0,S_1`; the expanded degree-two through degree-four
proofs verify the mechanism. We prove `S_d` for every finite `d` by
induction.

Assume `S_j` for `j<d`, with `d>=2`.

## 1. Projection Grassmannians in degree d-1

For the unitary orbit map onto a fixed-trace projection Grassmannian, the
inverse fibres are products of corner unitary groups. By `S_(d-2)` they
are `(d-2)`-connected and equi-`LC^(d-2)`. The inverse map is lower
semicontinuous and the close-projection lemma supplies pointwise
conjugators close to the identity.

Controlled Michael selection with index `d-2` lifts every sufficiently
small projection `S^(d-1)` to a small unitary `S^(d-1)`. Fill that lift
using the top-degree modulus in `S_(d-1)` and conjugate the base
projection. The ordinary Michael theorem with the same index lifts an
arbitrary projection `S^(d-1)`; Jekel contracts the lift. Hence fixed-
trace Grassmannians are `(d-1)`-connected and equi-`LC^(d-1)`, uniformly
after normalized-corner scaling and the small-corner diameter split.

Translated superprojection values `P(h,q;s)` inherit the result whenever
`tau(h)<=s/2` and `s<tau(q)`.

## 2. The S^d carrier and pair lifts

For a small `x:S^d->Nq`, use the inclusive high spectral projection and
the lower-semicontinuous constant-trace superprojection multifunction.
Step 1 supplies exactly the `(d-1)`-connectivity and equi-`LC^(d-1)`
required by Michael selection with index `d-1` over `S^d`. Thus one
selects a carrier of trace at most `2delta^2/kappa^2` and operator residual
at most `kappa`.

After direct rotation, the carrier and partial-isometry conjugator
multifunctions have products of corner unitary groups as fibres. By
`S_(d-1)` they again satisfy the hypotheses for Michael index `d-1`.
Select both unitary `S^d` lifts, contract them by Jekel, and substitute.
The represented frame stays on the selected carrier, so the fill radius
is at most `2sqrt(2)delta/kappa` in every degree.

With `kappa=epsilon_0/40` and
`delta=epsilon_0^2/1000000`, the direct-rotation collar and localized fill
lie in the `epsilon`-ball. This proves the local part of `S_d` with the
same modulus (AD-1).

## 3. Global connectivity

For an arbitrary frame `S^d`, its unitary-conjugator multifunction has a
corner unitary stabilizer. By `S_(d-1)`, Michael index `d-1` selects a
unitary lift; Jekel contracts it. Thus the Stiefel space is `d`-connected.
This completes the finite induction. No infinite-dimensional selection
theorem or degree-independent hidden LC modulus is used: at stage `d`,
only the finitely many moduli through degree `d-1` enter existence, while
the explicit frame radius comes solely from carrier trace.