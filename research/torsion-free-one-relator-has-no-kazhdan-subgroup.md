---
rg: 2
id: torsion-free-one-relator-has-no-kazhdan-subgroup
kind: claim
title: No torsion-free one-relator group contains a nontrivial finitely generated Kazhdan subgroup
invalidates: [nonsofic-one-relator-via-kazhdan-subgroup-embedding]
distinct_from:
  nonsofic-one-relator-relator-has-primitivity-rank-two: that identifies the relator invariant a counterexample must have and supplies the torsion-freeness; this is the subgroup obstruction that follows, and it is what actually blocks the embedding strategy.
  fournier-facio-torsion-free-skeleton: that records the structure of a published torsion-free nonsofic group; this is a statement about what one-relator groups cannot contain, and its role here is to say that that group is not among their subgroups.
  bekka-valette-amenable-t-dichotomy: that is the amenable-versus-(T) dichotomy used elsewhere in this graph for representation-theoretic purposes; this is a local-indicability obstruction inside one-relator groups and uses only that (T) passes to quotients and `Z` fails it.
  degree-one-assembly-surjective-torsion-free: that is a surjectivity statement about degree-one assembly over torsion-free groups; this is a subgroup-exclusion statement inside torsion-free one-relator groups. They share the hypothesis "torsion-free" and no machinery — no assembly map, K-theory or index appears here.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

ESTABLISHED.  Let `G` be a torsion-free one-relator group.  Then `G` has **no
nontrivial finitely generated subgroup with property (T)**.

## Proof

By Brodskii's theorem `G` is locally indicable: every nontrivial finitely
generated subgroup surjects onto `Z`.  Let `P <= G` be nontrivial, finitely
generated, with property (T).  Local indicability gives `P ↠ Z`.  Property (T)
passes to quotients, so `Z` would have property (T), which it does not.  ∎

(The statement is usually met as "no *infinite* f.g. (T) subgroup", but
torsion-freeness makes every nontrivial subgroup infinite, so the hypothesis is
free.)

## What it blocks

The most direct negative strategy for Pestov's Question 4.9 — soficity passes
to subgroups, so embed a known nonsofic group into a one-relator group — is
**closed for every nonsofic group currently known**, on both sides of the
torsion dichotomy:

- **Torsion-free target.**  Fournier-Facio's finitely presented torsion-free
  nonsofic group (arXiv:2608.02025, and [[fournier-facio-torsion-free-skeleton]]
  in this graph) is built around an infinite finitely generated property-(T)
  subgroup `Γ`, and the construction can be arranged so that the whole group has
  property (T).  Either way it is a nontrivial f.g. group with (T), so by the
  above it embeds in no torsion-free one-relator group.
- **Kun--Thom targets.**  [[kun-thom-nonsofic-wreath]] uses Kazhdan acting
  groups throughout; same obstruction, and the lamps are `Z/2`, which a
  torsion-free group cannot host either.
- **Torsion one-relator overgroup.**  Not an escape.  A one-relator group with
  torsion is virtually compact special (Wise), hence residually finite, hence
  sofic — and subgroups of sofic groups are sofic, so it contains no nonsofic
  group at all.

So the whole embedding lane dies, and it dies for a structural reason rather
than for want of cleverness: every known nonsoficity mechanism is
rigidity-driven, and the unresolved one-relator core is locally indicable, which
is the exact negation of rigidity in this sense.

## The consequence worth carrying forward

A negative answer to Question 4.9 needs a **nonsoficity mechanism compatible
with local indicability**.  None exists today.  That is a real research
direction and not merely a complaint: it says the next nonsofic construction, if
it is to be usable here, must avoid property (T) rather than exploit it.  The
route this claim kills is
[[nonsofic-one-relator-via-kazhdan-subgroup-embedding]].
