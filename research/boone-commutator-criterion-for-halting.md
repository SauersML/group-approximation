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

OPEN.  This is the target statement the whole Novikov--Boone chain converges
on, and it mentions no undecidability whatsoever:

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

## The remaining work

**The Britton core is proved** (`BooneGroupTower.conj_t_eq_iff`): adjoining `k`
with both associated subgroups equal to `A` and the identity identification,
conjugation by `k` fixes exactly the image of `A` -- so `k^{-1} g k = g` if and
only if `g in <<t>>`.  That was the step this entry expected to be the
delicate one, and it is the easiest Britton application in the chain: one
stable letter, one syllable.  Combining it with
[[boone-tower-good-subgroup-transport]],
[[boone-halting-subgroup-is-normal-closure]] and `of_mem_basisSubgroup_iff`
from [[free-subbasis-subgroup-calculus]] gives
`(a,b) in H_M <-> [k, t(a,b)] = 1`.  Estimated cost: about 200 new lines.
