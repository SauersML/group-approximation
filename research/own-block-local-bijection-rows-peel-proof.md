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
is a bijection, so `E` is a bijective cellular automaton fixing the second
coordinate. By Curtis--Hedlund--Lyndon its inverse `E^{-1}(Z,Y) =
(Phi_Y^{-1}(Z), Y)` is a cellular automaton.
Then `D = F o E^{-1}` has the form `D(Z,Y) = (Z, T_Z(Y))`, a finite-memory map
fixing the certificate `Z`, and `T_0 = F'`. Since `F = D o E` and `E` is
bijective, `F` is injective iff `D` is and surjective iff `D` is. `D` injective
forces its fiber `F' = T_0` to be injective. If `D` is surjective, every fiber
is; conversely, by `nonlinear-certificate-fibers-are-all-surjective-or-all-strict`,
the surjective `Z = 0` fiber `F'` makes `D` surjective. Hence `F'` is injective,
`F` is surjective iff `F'` is, and `F'` surjective implies `F` surjective. Valid
nonlinear instances are composites of track shears and the single-track
order-three control, both in Section 1 of the artifact.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 7.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Correction: the last sentence, on graded-nilpotent own parts, is withdrawn. Nonlinear `N` does not invert as `sum (-N)^(k)`; use track shears instead.

**Resolved 2026-09-12** (gk-p-tails). The graded-nilpotent sentence has been replaced by the valid instances above.
