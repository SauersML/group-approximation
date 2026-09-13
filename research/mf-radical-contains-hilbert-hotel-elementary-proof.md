---
rg: 2
id: mf-radical-contains-hilbert-hotel-elementary-proof
kind: route
title: Transfinite induction along the Hilbert-hotel chain
target: mf-radical-contains-hilbert-hotel-elementary-subgroup
requires:
  - hilbert-hotel-radical-is-smallest-directly-finite-quotient
  - relative-torsion-defect-mf-radical-step
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

Full derivation in artifact section 4. Induct on the chain `hh_a` of the first required claim, the
statement at stage `a` being `EL_n(R, hh_a) <= Rad_MF(EL_n(R))`.

**Stage 0.** `hh_0 = 0` and `EL_n(R,0) = 1`.

**Successor.** Let `(sbar,tbar)` be a one-sided pair of `R/hh_a` with defect `ebar`, and lift
`s,t` to `R`. Then `ts - 1 in hh_a`, and `m e in hh_a` where `m` is the additive order of
`ebar`, which is finite because the additive group of `R` is torsion. The second required claim,
applied with `J = hh_a`, gives `EL_n(R, ReR + hh_a) <= Rad_MF(EL_n(R))`. Now `hh_(a+1)` is by
definition the sum of the ideals `ReR + hh_a` over all one-sided pairs of `R/hh_a`, every element
of a sum of ideals is a finite sum of elements of the summands, and
`e_ij(a_1 + ... + a_r) = e_ij(a_1) ... e_ij(a_r)`; so the normal closures multiply and
`EL_n(R, hh_(a+1)) <= Rad_MF(EL_n(R))`.

**Limit.** Each entry of an elementary generator of `EL_n(R, hh_l)` already lies in some `hh_a`
with `a < l`, so `EL_n(R, hh_l)` is the union of the `EL_n(R, hh_a)`.

The chain stabilises at `hh(R)`, which gives the claim.
