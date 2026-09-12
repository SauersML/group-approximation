---
rg: 2
id: uniform-wp-bound-excludes-bh-universal-targets
kind: claim
title: No class of groups with a uniform recursive word-problem bound contains a Boone-Higman envelope for every input
distinct_from:
  decidable-fp-groups-need-not-embed-in-rational-group: that is the single-exponential instance of this statement, for groups of rational Cantor homeomorphisms; this is the general principle, with the target class and the bound both arbitrary, and that claim follows from it.
  compilers-cannot-drop-the-decidability-hypothesis: that is the qualitative screen -- the data forces its input to have solvable word problem, so no argument uniform in a finite presentation can supply it; this is the quantitative refinement, bounding how *hard* the target's word problem must be allowed to get.
  kms-arbitrarily-hard-fp-rf-groups: that is the imported realization theorem supplying arbitrarily hard finitely presented residually finite groups; this is the consequence for target classes, and it consumes that claim.
  simple-envelope-forces-solvable-word-problem: that runs in the other direction, deducing decidability of a subgroup from finite presentation and simplicity of an envelope; this bounds the complexity an envelope class must be able to realize.
artifacts:
  - research/artifacts/boone-higman-complexity-wall-2026-09-11.md
---

ESTABLISHED. Let `g` be recursive and non-decreasing and write, as in
`kms-arbitrarily-hard-fp-rf-groups`,

```text
F(g) = { L : L decidable in time C*g(C*n) + C*n + C for some C }.   (UWB1)
```

Let `C` be any class of finitely generated groups such that every `H` in `C`
has, for some finite generating set, word problem in `F(g)`. Then there is a
finitely presented residually finite group with decidable word problem that
embeds in **no** member of `C`.

In particular `C` contains no Boone--Higman envelope for every finitely
generated group with solvable word problem: some admissible input has no
overgroup in `C` at all, let alone a finitely presented simple one.

The constant is allowed to depend on the group and on the generating set. What
is forbidden is a single recursive `g` serving the whole class.

## What this rules out, and what it does not

*Rules out.* Any proposed universal target family whose word problem is
uniformly bounded by a recursive function: in particular every family with
word problem in `P`, in `coNP`, or in `EXP`. Taking `g(n) = 2^n` and combining
with `rational-homeomorphism-subgroups-have-exponential-wp` recovers
`decidable-fp-groups-need-not-embed-in-rational-group` as the special case;
that claim keeps its own route and is not re-derived here.

*Does not rule out.* The twisted Brin--Thompson programme, or any other
programme in which the target is built from an actor that already contains the
input. There the target's complexity rises with the input's, and no uniform
`g` is claimed. The correct reading is therefore a constraint on the *shape*
of a universal construction rather than a refutation of any live route: the
construction must transport the input's word-problem complexity into the
target, so no step may pass through a family with a fixed complexity ceiling.

This sharpens `compilers-cannot-drop-the-decidability-hypothesis` from "the
construction must consume the decidability algorithm" to "the construction
must consume it in a way that preserves arbitrarily high complexity".

DERIVATION
uniform-wp-bound-excludes-bh-targets-proof
