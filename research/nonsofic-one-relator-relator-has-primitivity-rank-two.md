---
rg: 2
id: nonsofic-one-relator-relator-has-primitivity-rank-two
kind: claim
title: A nonsofic one-relator group has primitivity rank exactly two, hence is torsion-free and locally indicable
distinct_from:
  nonsofic-one-relator-group: that asks for such a group to exist and is open; this is a necessary condition on any that does, and is closed. It constrains the search space without populating it.
  torsion-free-one-relator-has-no-kazhdan-subgroup: that excludes property-(T) subgroups and is what blocks importing the known nonsofic witnesses; this pins the relator invariant and the torsion-freeness that the other one takes as its hypothesis.
  torsion-free-countable-non-mf: that asserts a torsion-free countable group is not MF; this asserts that a hypothetical nonsofic one-relator group is torsion-free. Torsion-freeness is the conclusion here and a hypothesis there, and MF does not appear here at all.
  torsion-free-finitely-presented-non-mf: that is an existence statement about non-MF groups and is a root of this graph; this is a necessary-condition statement about nonsofic one-relator groups. Neither soficity nor one-relator presentation figures there, and MF does not figure here.
  torsion-free-higman-embedding: that is an embedding theorem placing recursively presented torsion-free groups inside finitely presented ones; this constrains the relator of a hypothetical nonsofic one-relator group. Both mention torsion-freeness and nothing else.
  degree-one-assembly-surjective-torsion-free: that is a surjectivity statement about degree-one assembly holding for every torsion-free group; this derives torsion-freeness (among other things) for a hypothetical nonsofic one-relator group. Torsion-freeness is that one's hypothesis and this one's conclusion; no assembly map appears here.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that constrains a hypothetical counterexample by showing all elements outside its derived Linton radical survive in a sofic quotient; this independently constrains its relator by primitivity rank and supplies torsion-freeness and local indicability.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

ESTABLISHED.  Let `G = F/<<w>>` be a one-relator group and `π(w)` the
primitivity rank of `w` — the least rank of a subgroup of `F` containing `w` as
an imprimitive element.  If `G` is **not sofic**, then

    π(w) = 2 ,

and consequently `G` is torsion-free and locally indicable.

## Proof

Residually finite groups are sofic, so it suffices to show `π(w) ≠ 2` implies
`G` residually finite.  The three remaining values are each covered:

- **`π(w) = 1`.**  This says `w` lies in a rank-one subgroup as an imprimitive
  element, i.e. `w = u^m` with `m >= 2` is a proper power.  Then `G` is a
  one-relator group **with torsion**, and by Wise's theorem such groups are
  virtually compact special, hence residually finite.
- **`π(w) >= 3`.**  By Louder--Wilton this is exactly the condition that the
  presentation have **negative immersions**.  Linton (*One-relator
  hierarchies*, Duke Math. J. **174** (2025) no. 4) proves one-relator groups
  with negative immersions are hyperbolic and virtually compact special,
  resolving the Louder--Wilton conjecture; residual finiteness follows.
- **`π(w) = ∞`.**  By Puder--Parzanchevski this says `w` is primitive in `F`,
  so `G` is free, hence residually finite.

For the consequences: `π(w) = 2` excludes `π(w) = 1`, so `w` is not a proper
power and `G` is torsion-free by the one-relator torsion theorem.  Brodskii's
theorem (also Howie) says every torsion-free one-relator group is locally
indicable.  ∎

## Why this is the most useful single constraint in the region

It reduces Pestov's Question 4.9 from all one-relator presentations to the
single primitivity value at which no residual-finiteness theorem is available,
and it does so with a mechanism — virtual specialness — that is not going to be
weakened.  Everything downstream in this region assumes torsion-freeness and
local indicability on its strength: in particular
[[torsion-free-one-relator-has-no-kazhdan-subgroup]], which is what stops the
known nonsofic groups from being imported by subgroup embedding.

A caution about direction.  This says nothing about whether a counterexample
exists; a great many `π(w) = 2` relators give obviously sofic groups
(`[a,b]` gives `Z²`).  Its content is that the *only* place a counterexample
can live is a regime where the corpus's usual soficity certificate — residual
finiteness — is unavailable by construction, and where the group is
simultaneously forbidden the rigidity that every known nonsofic group uses.
Those two facts pull in opposite directions and are the reason the question is
hard rather than merely open.

Combined with
[[one-relator-fox-magnus-descent-to-derived-linton-radical]], the target is
sharper still: a hypothetical counterexample has `pi(w) = 2` and any
obstruction must survive inside the derived subgroup of its infinitely
generated, normally one-generated Linton radical.  In the `k = 1` case that
radical is already perfect.
