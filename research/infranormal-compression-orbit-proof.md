---
rg: 2
id: infranormal-compression-orbit-proof
kind: route
title: A strict compressor has no power in the subgroup
target: infranormal-nonnormal-has-infinite-compression-orbit
requires: []
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Direct establishment; `requires: []` is a proof commitment.  Nothing external
is used, and no property of `G` beyond the two hypotheses.

**A strict compressor exists.**  If `g Gamma g^(-1) = Gamma` for every
`g in P_Gamma`, then `P_Gamma <= N_G(Gamma)`; a semigroup contained in a
subgroup generates a subgroup contained in it, so `G = <P_Gamma> <= N_G(Gamma)`
and `Gamma` is normal, contrary to hypothesis.  Fix `g in P_Gamma` with
`g Gamma g^(-1) < Gamma` strictly.

**No power of `g` lies in `Gamma`.**  Conjugating `g Gamma g^(-1) <= Gamma`
by `g` repeatedly gives

    Gamma >= g Gamma g^(-1) >= g^2 Gamma g^(-2) >= ... >= g^k Gamma g^(-k).

If `g^k in Gamma` for some `k >= 1` then `g^k Gamma g^(-k) = Gamma`, so the
chain begins and ends at `Gamma` and each of its inclusions is an equality; in
particular `g Gamma g^(-1) = Gamma`, contradicting strictness.  Taking `k = 1`
in the conclusion also shows `g not in Gamma`, and `g^k != 1` for `k >= 1`
since `1 in Gamma`, so `g` has infinite order.

**Infinite orbit and infinite index.**  In `X = G/Gamma`, `g^n Gamma = g^m
Gamma` forces `g^(n-m) in Gamma`, hence `n = m`.  So `n |-> g^n Gamma` is
injective, the `<g>`-orbit of the base point is infinite, and
`[G : Gamma] = |X|` is infinite.

The finite-index case falls out of the last line, and can also be seen the
way `finite-infranormal-subgroup-is-normal-proof` sees the finite-order case:
if `[G : Gamma] < infinity` then `g Gamma g^(-1) <= Gamma` between subgroups
of equal finite index is an equality, so `P_Gamma = N_G(Gamma)` and
infranormality forces normality.
