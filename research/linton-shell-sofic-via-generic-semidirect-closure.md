---
rg: 2
id: linton-shell-sofic-via-generic-semidirect-closure
kind: route
title: Get the Linton shell from closure of soficity under semidirect products
target: linton-shell-sofic
requires: []
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

The shell is `E ≅ R ⋊_α F₀` with `F₀` free.  Free groups are sofic; so if the
class of sofic groups were closed under semidirect products, soficity of `R`
alone ([[linton-radical-sofic]]) would give soficity of `E`, and with the
reduction all of [[one-relator-groups-sofic]] would follow from a statement
about the radical.

**Dead: the closure property is false**, by
[[sofic-semidirect-product-closure-fails]].  Kun--Thom's Theorem A produces a
nonsofic `( ⊕_{G/Γ} Z/2Z ) ⋊ G` in which the normal factor is abelian and the
acting factor is residually finite — both sofic by wide margins.  The failure is
not at the edge of the hypotheses; it is at the strongest hypotheses anyone would
put on the factors.

## Why it is recorded rather than omitted

Because the shape of the shell invites it.  "Free acting on something" reads as
tame, and until August 2026 a working mathematician could have assumed the
closure without anyone objecting.  Writing the route down and killing it by
reference means the next session reads the kill instead of re-deriving the hope.

## What survives the demolition

The kill is about hypotheses on the **factors**.  Nothing here refutes a theorem
whose hypothesis is on the **action** — Kun--Thom's counterexamples fail exactly
such a hypothesis, since their coordinate action is not sofic
(`sofic-action-permanence` records that in the wreath setting).  Nor does
anything refute a theorem restricted to free acting groups, which is unexplored:
Kun--Thom's acting groups have property (T).  The live successors are therefore
`linton-shell-sofic-via-sofic-action`, which puts the hypothesis where the
counterexamples put the failure, and — if anyone wants the stronger statement —
a free-acting-group closure theorem, which would be at least as hard as Pestov's
question itself and so is a target rather than a lemma.

The explicit embedding in
[[one-relator-fox-magnus-descent-to-derived-linton-radical]] does not revive
this route.  It proves `E/R'` residually finite without extension closure; the
passage back across `R'` would again require exactly the action-sensitive input
that this invalidated shortcut omits.
