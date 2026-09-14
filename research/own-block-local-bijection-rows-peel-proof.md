---
rg: 2
id: own-block-local-bijection-rows-peel-proof
kind: route
title: Straighten the own-block bijection to a certificate map and apply the fiber dichotomy
target: own-block-local-bijection-rows-peel
requires:
  - nonlinear-certificate-fibers-are-all-surjective-or-all-strict
artifacts:
  - research/artifacts/corrected-tail-peeling-boundary-2026-09-12.md
---

Section 1, Lemma 1.1 of the artifact. Put `E(X,Y) = (Phi_Y(X), Y)`. Each `Phi_Y`
is a bijection with a uniform local inverse, so `E` is a bijective cellular
automaton fixing the second coordinate, with `E^{-1}(Z,Y) = (Phi_Y^{-1}(Z), Y)`.
Then `D = F o E^{-1}` has the form `D(Z,Y) = (Z, T_Z(Y))`, a finite-memory map
fixing the certificate `Z`, and `T_0 = F'`. Since `F = D o E` and `E` is
bijective, `F` is injective iff `D` is and surjective iff `D` is. By
`nonlinear-certificate-fibers-are-all-surjective-or-all-strict`, `D` injective
forces `F' = T_0` injective, and `D` is surjective iff its `Z = 0` fiber `F'` is
surjective. Hence `F'` is injective, `F` is surjective iff `F'` is, and `F'`
surjective implies `F` surjective. The graded-nilpotent inverse
`sum_{k<D} (-N_Y)^{(k)}` is a finite composite of local functions, so a
graded-nilpotent own part is a valid `Phi_Y`.
