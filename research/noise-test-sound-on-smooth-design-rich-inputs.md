---
rg: 2
id: noise-test-sound-on-smooth-design-rich-inputs
kind: claim
title: The Braverman--Khot--Minzer reduction stays sound when richness is weakened to a smooth low-degree pairing design
distinct_from:
  rich-2to1-conjecture-is-equivalent-to-ugc: that is the published equivalence for fully rich instances; this identifies the two properties of the pairing distribution the soundness proof uses and shows any family with both suffices.
  separated-small-pairing-families-defeat-the-noise-test: that is the obstruction for small separated families; this is the positive transfer for families that are designs of strength 8d+1 with the pull-back density comparison, which by pullback-smoothness-needs-exponentially-many-pairings are always exponentially large.
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

**ESTABLISHED (transfer of a published proof).** Call a family `F` of perfect
pairings of `[2n]` **`t`-wise uniform** when every partial matching with at most
`t` pairs lies in a random member of `F` with the same probability as in a
uniform perfect matching. Call it **`(K,m,C_0)`-smooth** when the pull-back
distribution `nu_(F,m)` has density at most `C_0 m^(-2n)` at every `K`-roughly
balanced point.

Fix the parameters `m, delta, zeta, d` of BKM's main analytic lemma (ECCC
TR19-141, Lemma 3.1) and `C_0 >= 1`. For `n` large, the lemma's conclusion holds
for `pi` drawn from any `(8d+1)`-wise uniform, `(K,m,C_0)`-smooth family, with
uniformly random right labels. Its high-degree threshold `gamma` also depends
on `C_0`. Consequently their Section 5 soundness argument applies verbatim to
2-to-1 instances whose pairing family at every left vertex has these two
properties.

The proof audits every use of uniformity: degree-`2d` and degree-`8d`
expectations in Lemmas 4.6, 4.9 and 4.10, which a design matches exactly, and
the density comparison in Lemma 4.12, which smoothness supplies. All other
lemmas concern `f` alone or the uniform measure alone. Richness is not used in
completeness or folding.

This is a transfer: BKM's lemmas are imported, not reproved.
