---
rg: 2
id: kazhdan-relations-coamenable-subrelations-locally-kazhdan
kind: claim
title: A co-amenable subrelation of an ergodic Kazhdan relation is an ergodic finite-index Kazhdan subrelation on a positive piece, so no Haagerup or treeable subrelation is co-amenable
distinct_from:
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: that is the subgroup statement, where co-amenability forces finite index globally and simplicity forces equality; this is the equivalence-relation statement, where only local finite index holds (proper co-amenable subrelations exist) and the surviving obstruction is the (T)/(H) exclusion.
  no-invariant-mean-on-coset-space: that is finite index for co-amenable subgroups of Kazhdan groups; this is its measured-relation analogue, with Hilbert-bundle co-amenability and a positive invariant piece.
  non-ce-relation-is-not-treeable: that says a relation with non-CE algebra is not treeable, a property of the whole relation; this says a treeable subrelation can never be co-amenable inside a Kazhdan relation, a property of the pair.
  kazhdan-groupoid-cnd-criterion-and-t-h-exclusion: that imports the groupoid (T)/(H) facts, including that the whole Kazhdan orbit relation is not Haagerup; this proves the statement for co-amenable subrelations, which needs local finite index, reductions, choice functions and induced cnd functions.
artifacts:
  - research/artifacts/kazhdan-relation-coamenability-collapse-2026-09-17.md
---

**ESTABLISHED.** Let `R` be an ergodic p.m.p. countable equivalence relation with property (T) on a diffuse
standard probability space `(X, mu)`.

Call `S <= R` *co-amenable* if the representation `lambda_(R/S)` of `R` on the Hilbert bundle
`x -> l^2([x]_R / S)` almost contains unit invariant sections (AD05 Def 4.2(3)). The maps along `R` are identities.
Følner and Reiter data on `[x]_R / S` produce such sections.

1. **(Local finite index.)** If `S` is co-amenable, there are an `S`-invariant Borel `A` with `mu(A) > 0` and an
   integer `k >= 1` such that `S|_A` is ergodic and a.e. class of `R|_A` is the union of exactly `k` classes of `S`.
2. **(Locally Kazhdan.)** For that `A`, `S|_A` has property (T).
3. **(Exclusion.)** No subrelation with the Haagerup property is co-amenable in `R`. In particular no treeable
   subrelation is, and no factor-of-iid treeing is.
4. **(Kazhdan groups.)** If `G` is an infinite Kazhdan group and `G -> (X, mu)` is essentially free, ergodic and
   p.m.p. (for example a Bernoulli shift), then `R_G` satisfies the hypotheses, so 1--3 apply to `R_G`.

Global finite index is false: `S = (R ∩ A x A) ∪ Delta` is co-amenable of infinite index (artifact Section 6.1).
So the finite-index form in `research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md`
line 82 must be read locally.

**Why it matters.** It proves the relation-level collapse that the percolation-treeing attempt on
`bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups` marked "not proved here". It completes condition 4 of
Section 4 of that artifact. Every co-amenability-based ascent of a lower bound (Rokhlin, f-invariant, sofic, or
Bernoulli extension entropy) onto a Kazhdan orbit relation dies at its input step, if its source subrelation is
Haagerup, treeable, a Gaboriau--Lyons treeing, or the orbit relation of a free action of a Haagerup group. The
co-amenable Følner data give an invariant unit section (property (T)). That section forces a positive piece on which
the source is Kazhdan, and AD11 Thm 9.2 forbids (T) and (H) together.

This does not claim that every lower-bound mechanism needs co-amenability.

## Attempts

- **Proof (a-gs-pull-5, 2026-09-17).** Route `kazhdan-relations-coamenable-subrelations-locally-kazhdan-proof`.
  Full proofs are in artifact Sections 3--5. Not proved: the measurable Day--Namioka step from invariant fields of
  means to the Hilbert form, and any entropy transfer along the finite-index piece (artifact Section 8).
