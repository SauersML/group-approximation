---
rg: 2
id: self-square-embedding-gives-a-kazhdan-clifford-base
kind: claim
title: A group embedding its own direct square is a Kazhdan-Clifford base, and the result still has torsion
distinct_from:
  kazhdan-clifford-non-mf-construction: that is the construction itself, taking a proper self-embedding and a protected element as given; this says where such a pair comes from -- one injection of the direct square supplies both -- and that the resulting group still contains an involution, so the substitution buys nothing for the torsion-free question.
  fournier-facio-torsion-free-skeleton: that records the published torsion-free nonsofic group and the simple subgroup in its compression defect; this is the abstract algebra of the remark that proposes reusing that group as a base, and it assumes nothing about it.
  torsion-free-finitely-presented-non-mf: that root asks for a torsion-free finitely presented non-MF group; this claim's second half is a negative result about one proposed route to it.
  torsion-free-higman-embedding: that is an embedding theorem -- every recursively presented torsion-free group embeds in a finitely presented one -- and it is literature-plausible but unverified here; this needs no embedding theorem at all, only an injection of a group's own direct square into itself, and it exhibits a group admitting one outright.  The universality statement that would connect them appears here only as the explicit hypothesis of a single implication.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Monsters/FournierFacioRealization.lean
  - GroupApproximation/Monsters/RealizationEmbedding.lean
---

Let `P` be finitely presented with property (T), and suppose there is an
injective homomorphism `f : P x P -> P`.  Put `alpha = f o inl` and, for any
`b != 1`, `a = f(1, b)`.  Then:

- `alpha` is an injective endomorphism of `P` and `a` lies **outside** its
  image, so `(alpha, a)` satisfies the hypotheses of the Kazhdan--Clifford
  construction; the two ranges are disjoint and commute elementwise, which is
  the remark's `P_1 x P_2 <= P`;
- consequently the extension `E(P, alpha, a)` is finitely presented, contains
  `P`, and is not CDE-operator-MF;
- and `E(P, alpha, a)` **contains a nontrivial involution** — the distinguished
  central mark — *whatever the base*.

Such groups `P` exist unconditionally: an explicit group embedding its own
direct square is exhibited, so the hypothesis is not vacuous.  What is *not*
proved is that the specific published group has this property; see below.

## What this settles, and what it deliberately leaves outside

This is manuscript Remark `rem:ff-realization` ("a small-cancellation
realization"), which reports a suggestion of Fournier-Facio: replace the affine
base of the explicit construction by the finitely presented torsion-free
property-(T) group of the torsion-free nonsofic paper, which contains a copy of
every finitely presented torsion-free group and hence a direct square of itself.

The remark is **load-bearing for no numbered result**: it states no theorem,
carries no `\leanverified` badge, and is referenced only by a `cf.` pointer from
the Questions preamble.  Its one mathematical deduction is the first bullet
above, and that is proved here from the abstract injection alone — `f` is data,
not a literature theorem, and no property of any particular group is assumed.

Two separations are kept explicit rather than blurred:

- **Mathematics, proved.**  The step from "contains a copy of every finitely
  presented torsion-free group" to "contains its own square" is closure of that
  class under binary direct products, and both closure facts (finite
  presentation and torsion-freeness of a product) are in the repository, so the
  implication is proved outright.
- **Literature, not proved.**  Existence of a finitely presented torsion-free
  property-(T) group universal for finitely presented torsion-free groups
  (Higman; Belegradek--Szczepanski; Chiodo, as used by Fournier-Facio) appears
  only as an explicit hypothesis of that one implication.  Nothing in the
  manuscript's numbered development depends on it.

The third bullet is the reason the whole substitution changes nothing for the
torsion-free programme: the mark is an involution regardless of the base, so a
torsion-free base does not yield a torsion-free `E`.  Theorems A, D and E stay
proved for the affine base.
