---
rg: 2
id: literal-group-not-sofic
kind: claim
title: The literal finitely presented non-MF group is not sofic
refuted_by: literal-group-sofic
root: true
distinct_from:
  literal-group-sofic: That claim asserts soficity of `E`; this is its negation, kept as a separate node because the kernel only understands implications and both sides now have live routes.
  hyperlinear-nonsofic-group: That root asks for any hyperlinear nonsofic group; this one asks whether the specific literal group `E` fails soficity.
  wreath-not-sofic: That concerns the wreath candidate of the flexible-side program; this concerns the literal forty-one-relator group.
  literal-central-mark-corona-invisible: That established claim is the operator-norm corona obstruction that makes `E` non-MF; failing MF says nothing about permutation approximation, which is what this claim denies.
  literal-group-fails-mf-conventions: That claim enumerates the MF conventions `E` fails; soficity is a permutation-approximation property that none of those conventions decides.
  torsion-free-finitely-presented-non-mf: That claim asks for a torsion-free non-MF example; this one asks whether the specific literal group, which has torsion, fails soficity.
  literal-mf-radical-exact: That claim asks for an exact computation of the MF radical of `E`; this one asks whether `E` admits permutation microstates at all.
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - non_mf_groups_exist.tex
---

The literal finitely presented group `E` is not sofic; equivalently, it would
be a finitely presented non-sofic group.

**REFUTED the same day it was posed (2026-08-14).**  `literal-group-sofic` is
established: `E` IS sofic, by the block-tower argument of
`notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`.  The node is kept so that the
invalidation of `literal-nonsofic-via-stable-central-quotient` has a named
victim, and because the reasoning that motivated it is still informative:

`E` is a central extension `1 -> Z/2 = <w> -> E -> E/<w> -> 1` of a finitely
presented group whose central involution dies in every finite quotient — the
configuration of `gohla-thom-stable-base-nonsofic-extension` and of the
Deligne extensions used as non-soficity candidates.  Since `E` is sofic, the
contrapositive says that `E/<w>` fails at least one of that theorem's three
base hypotheses: residual finiteness of finite type, the dimension-2
cosystolic inequality, or stability in finite actions.  Which one fails is
open, and the first is exactly the input `literal-mark-quotient-mf` needs.
