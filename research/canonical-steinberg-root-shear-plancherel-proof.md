---
rg: 2
id: canonical-steinberg-root-shear-plancherel-proof
kind: route
title: Fourier-expand the finite row-root group and conjugate term by term
target: steinberg-root-shear-plancherel-covariance
requires:
  - gowers-hatami-finite-group-hs-stability
  - near-regular-finite-character-fixes-plancherel-types
---

Same-row Steinberg roots commute and add, so `(a,c)` maps homomorphically to
`x_12(a)x_13(c)`.  The standard map from the Steinberg group to the
elementary matrix group reads `a` and `c` in the `(1,2)` and `(1,3)` matrix
entries, proving injectivity.  Direct elementary-matrix multiplication, or
the Steinberg commutator relation, gives `(PSH3)`; `(PSH1)` makes its right
side stay in the same finite subgroup.

On an exact representation of `H_(V,W)`, ordinary finite Fourier inversion
makes `(PSH6)` its complete family of character projections.  For the
microstates, expand every product, adjoint, and sum of the operators in
`(PSH6)`.  The exact character-orthogonality calculation leaves the desired
PVM identity, while the remaining finitely many terms are bounded by the
complete-table multiplication defects.  This proves the `o(1)` PVM
assertion.  Taking normalized traces in `(PSH6)` and using `(PSH5)` leaves
only the identity term, proving `(PSH7)`.

Finally conjugate `(PSH6)` by `U_n(q_r)`.  Replace each conjugated word by
the right side of `(PSH3)`, paying the finite word-table defect, and change
variables by the bijection `alpha_r`.  The result is precisely the Fourier
sum indexed by `theta compose alpha_r^-1`, proving `(PSH8)`.

Alternatively, Gowers--Hatami exactifies the complete finite table and
`near-regular-finite-character-fixes-plancherel-types` gives `(PSH7)` on the
exactification.  The direct Fourier calculation above additionally records
the concrete shear covariance needed downstream.
