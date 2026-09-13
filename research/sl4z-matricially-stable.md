---
rg: 2
id: sl4z-matricially-stable
kind: claim
title: SL_4(Z) is point-norm matricially stable
distinct_from:
  sln-z-flexibly-hs-stable: that is flexible stability in normalized Hilbert--Schmidt norm, relevant to hyperlinearity; this is point-norm operator-norm stability without padding, relevant to MF of the reduced algebra.
---

OPEN.  Every operator-norm asymptotic homomorphism
`phi_n : SL_4(Z) -> U(k_n)` is pointwise close to genuine unitary
representations `pi_n : SL_4(Z) -> U(k_n)` of the same dimensions.

By `matricially-stable-overgroups-of-sl4z-are-not-reduced-mf` a positive answer
makes `C*_r(SL_4(Z))` not MF (`sl4z-reduced-cstar-is-not-mf`), turning the
Magee--de la Salle obstruction for genuine representations into an obstruction
for all MF models.

## Attempts

* **Dadarlat's cohomological obstruction.**  Would refute the claim if it
  applied.  `SL_4(Z)` is residually finite, hence an MF group, and linear, hence
  uniformly embeddable and admitting a gamma-element, so Dadarlat's Theorem 1.1
  (`dadarlat-matricial-stability-obstruction`) gives non-stability as soon as
  `H^(2k)(SL_4(Z); Q) != 0` for some `k >= 1`.  The rational cohomology of
  `SL_4(Z)` (Lee--Szczarba) is recorded in the literature as concentrated in
  degrees 0 and 3; this lane has not re-read that source, so the obstruction's
  absence is unverified here.
* **Uniform (Ulam) stability of higher-rank lattices.**  Does not apply:
  Glebsky--Lubotzky--Monod--Rangarajan control almost-representations with
  small defect uniformly over all pairs of group elements, while an asymptotic
  homomorphism has only pointwise vanishing defect
  (`corona-defect-is-not-uniform`).
* **Almost-commuting unitaries on unipotent subgroups.**  `Z^2` is not
  matricially stable (Voiculescu's pairs), and `SL_4(Z)` contains commuting
  unipotent `Z^2`.  Matricial stability does not pass to subgroups; whether
  Steinberg relations such as `e_13 = [e_12, e_23]` rigidify the Bott-type
  winding obstruction in the ambient group is open.
