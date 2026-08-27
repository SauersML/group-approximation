---
rg: 2
id: boone-commutator-criterion-for-halting
kind: claim
title: Simpson's Theorem 8 - one commutator decides whether a modular machine halts
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: That is the undecidability statement and needs a machine with non-computable halting set plus finite presentability; this is the biconditional for an ARBITRARY modular machine, mentions no undecidability, and is the whole mathematical content of the chain.
  boone-tower-good-subgroup-transport: That is goodness of the halting subgroup inside the tower; this adjoins the final stable letter `k` and converts membership into a commutator identity.
artifacts:
  - GroupApproximation/Computability/BooneGroupTower.lean
  - GroupApproximation/Computability/BooneGroupMachineIndex.lean
---

ESTABLISHED (2026-08-16), `BooneGroupGoodness.conj_k_finalTw_eq_iff`.  This is
the target statement the whole Novikov--Boone chain converges on, and it
mentions no undecidability whatsoever:

> for every `M : ModularMachine` and every `(a, b) : N x N`,
> the commutator `[k, t(a,b)]` is trivial in `(G'_M)'` if and only if
> `M.Halts (a, b)`.

Here `(G'_M)'` is the tower of [[boone-hnn-tower-embeds-base-group]] with one
further stable letter `k` adjoined, with `A = B = <<t>>` and `phi = id`.

## Why this, and not the undecidability statement, is the real target

Stages S3--S7 of the roadmap produce this biconditional for an *arbitrary*
modular machine.  The undecidability capstone is then a two-line corollary,
which must be written only once
[[modular-machine-with-noncomputable-halting]] is available -- and that
statement is deliberately not present in Lean anywhere in this chain, not as a
hypothesis and not as a named predicate, so that no theorem in the repository
can silently depend on it.

## How it goes

`FinalGroup mm hM` is `G'_M` with `k` adjoined over `towerTSub`, both
associated subgroups equal and the identification the identity, and `finalTw`
is `t(α,β)` seen there.  `BooneGroupTower.conj_t_eq_iff` is the Britton core:
for that shape of extension, conjugation by the stable letter fixes exactly the
image of the associated subgroup, so `k^{-1} g k = g` iff `g ∈ <<t>>`.  It is
the easiest Britton application in the chain -- one stable letter, one
syllable.  Composing with
[[boone-tower-good-subgroup-transport]],
[[boone-halting-subgroup-is-normal-closure]] and `of_mem_basisSubgroup_iff`
from [[free-subbasis-subgroup-calculus]] gives
`(a,b) in H_M <-> [k, t(a,b)] = 1`.  `goodTower_machine` is what discharges
S4's hypothesis for an actual machine's identification list, which was the last
mechanical step either side of this statement.
