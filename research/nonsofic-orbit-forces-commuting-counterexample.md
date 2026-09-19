---
rg: 2
id: nonsofic-orbit-forces-commuting-counterexample
kind: claim
title: One nonsofic action of a sofic group forces two commuting sofic actions whose combination is nonsofic
distinct_from:
  coordinate-action-not-sofic: that is the input — a single nonsofic coset action of one explicit group; this is the general transfer principle that turns any such input into a commuting-actions counterexample, and it names no group
  gkp-sofic-action-toolkit: that is the imported external machinery; this is a new theorem proved from it
  commuting-sofic-actions-need-not-combine: that is the unconditional existence statement, which needs the Kun--Thom pair as well; this is the conditional transfer principle and is independent of whether any nonsofic action exists
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
  - research/artifacts/commuting-sofic-actions-note-2026-08-17.md
---

Let `G` be a countable sofic group and `H ≤ G` a subgroup such that the left
coset action `G ↷ G/H` is **not** sofic. Then there is a countable set `X`
carrying two commuting actions

```text
α_1 : G ↷ X,     α_2 : G ↷ X
```

such that `α_1` and `α_2` are both sofic — indeed both **free** — while the
combined action `α : G × G ↷ X` is not sofic.

The set is `X = (G × G)/ΔH` with `ΔH = {(h,h) : h ∈ H}`, the two actions are
left multiplication in each coordinate, and the combined action is left
multiplication by `G × G`, which is **transitive**. Proof:
`diagonal-coset-commuting-counterexample-proof`.

## The hypothesis is weaker than it looks

Transitivity of the bad action is free. By `gkp-sofic-action-toolkit`
(Proposition 2.15(2) with Proposition 2.16) an action is sofic iff each of its
orbits is, so **any** nonsofic action of a sofic group on a countable set
contains a nonsofic orbit, and that orbit is `G`-isomorphic to `G/H` for `H`
the stabilizer of any of its points. So the statement above is equivalent to:

> If a countable sofic group admits any nonsofic action on a countable set,
> then it admits two commuting free sofic actions whose combination is
> nonsofic.

## Scope — what this does not say

- It says nothing about whether nonsofic actions of sofic groups exist. That
  is a separate input (`coordinate-action-not-sofic`), and until August 2026
  it was open: the source paper itself records *"It is still open whether all
  actions by sofic groups are sofic."*
- It says nothing about the free-product form of the same permanence question
  (Gao–Kunnawalkam Elayavalli–Patchell Question 4.3, `α : ∗_i G_i ↷ X`). The
  construction here produces a direct product, not a free product, and no
  attempt has been made here to adapt it; Question 4.3 is untouched.
- It says nothing about the conjugation action of a sofic group on itself,
  which is the `H = G` case of the same construction and where the diagonal
  orbit degenerates to a point. That question stays open; a *negative* answer
  to the commuting question does not decide it, since the implication proved
  in the source runs the other way.
- `H` is necessarily not locally finite (Theorem 2.14), and in the known
  instance it is an infinite Kazhdan group.
