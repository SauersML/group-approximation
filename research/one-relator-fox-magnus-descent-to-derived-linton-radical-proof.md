---
rg: 2
id: one-relator-fox-magnus-descent-to-derived-linton-radical-proof
kind: route
title: Use purity of the Magnus relation module modulo k and separate the free shell orbitwise
target: one-relator-fox-magnus-descent-to-derived-linton-radical
requires: [linton-rational-derived-series-theorem, one-relator-soficity-localizes-at-rational-derived-stage, gkp-sofic-action-toolkit, gkp-wreath-permanence-theorem]
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

## Direct proof

The complete proof is written in the claim.  The prerequisites supply only
the external structure and permanence inputs:

- Linton supplies `N = <<r>>`, `R = N/W`, `H = F/N`, and
  `w in r^k[N,N]`, together with residual rational solvability of `H`;
- the finite-stage node supplies `E = R semidirect F0` with `F0` free;
- residual rational solvability of `H` makes it residually amenable and hence
  sofic;
- the GKP nodes certify that the regular action of a sofic group is sofic and
  that the corresponding restricted wreath product is sofic.

The new work is the exact kernel computation.  The Magnus relation sequence
has torsion-free additive cokernel `I_H`, which makes `D(N/N')` `k`-pure in
`(ZH)^d`.  That purity upgrades `D(f) in kM` to `[f] in kZH[r]`; since the
image of `W` is exactly that submodule, the mod-`k` Magnus kernel is `N'W`.
It follows that the descended kernel is exactly `R'`, not merely a subgroup
containing it.  The orbitwise finite-quotient argument for the free complement
then proves residual finiteness of `E/R'`.

No generic extension or semidirect-product closure principle is used.
