---
rg: 2
id: constant-bias-dkkms-selectors-put-np-in-rp
kind: claim
title: Every randomized polynomial-time constant-bias branch selector on the DKKMS doubled lift of regular Gap3Lin (lift value >= 1/2 + gamma with probability >= 1/poly on YES inputs, gamma <= 0.105, l >= 8) puts NP in RP, so under NP not in RP the constant-bias cell of H1 dies on DKKMS
distinct_from:
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is H1, a positive selector hole over all constructions and all cells; this is the negative statement for its constant-bias cell on DKKMS only, conditional on nothing but NP not in RP for its consequence.
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that kills the near-perfect cell (lift value 1 - xi) on DKKMS; this is the constant-bias cell (1/2 + gamma), where no rigidity-based decoder applies.
  selector-witness-hypotheses-collapse-to-selector-free-form: that proves Corollary D, the conditional reduction of this kill to a hardness and a selector-free statement on a class P; this is the unconditional kill statement itself.
  good-dkkms-orientations-admit-short-star-lists-on-hard-inputs: that was the first proposed pair of prerequisites (exact-kernel classes), refuted; this is the target those prerequisites served.
---

**OPEN.** One route so far:
`constant-bias-dkkms-selectors-put-np-in-rp-via-robust-uniqueness`.

## Statement

Use the doubled LEC of `value-free-star-list-references-put-np-in-rp` for
regular Gap3Lin through DKKMS, with parameters `(k, l, beta)`, `l >= 8`, and
constants `0 < gamma' < gamma <= 0.105` in the constant-bias cell. A
constant-bias selector is as in
`selector-witness-hypotheses-collapse-to-selector-free-form`.

**Claim.** If a constant-bias selector exists, then NP ⊆ RP.

## Status of routes

* The exact-kernel route through (SF_P) is dead
  (`exact-kernel-rank-does-not-exclude-flip-violators`).
* The robust-rank route through (SF_P^rob) is open. The route recorded here
  is a strengthening of its hardness half, (P1^RU), paired with the
  corresponding weakening of its structure half, (P2^RU). These are two
  independent prerequisites, and each one can fail.

## Attempts

* **2026-09-20, swarm-0917-w20-w20-ugc-pull (finite-models / transplanter).**
  Created as the explicit target of the constant-bias kill. Recorded the
  robust-uniqueness route and Lemma RU, which shows that the class of that
  route contains no input on which the known violator mechanism acts.
