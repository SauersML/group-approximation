---
rg: 2
id: one-sided-compression-nonsofic-criterion-proof
kind: route
title: Decompose both groups, match the transported components, select one, repair it
target: one-sided-compression-nonsofic-criterion
requires: [kun-expander-decomposition-formalized, kun-thom-expander-centralizer-formalized]
artifacts:
  - GroupApproximation/Criterion/CriterionAssembly.lean
  - GroupApproximation/Criterion/LocalCriterion.lean
  - GroupApproximation/Criterion/SelectionOutput.lean
---

## Why sufficient

Suppose `G` is sofic, with approximation `A`.

**Two decompositions.**  The first prerequisite, applied on the fixed
generating sets of the setup, gives an expander decomposition of `A` restricted
to `Γ` (`KunFixedDecomposition.expanderDecomposition` on `A.comap C.embedΓ`)
and one for the ambient generators.  They are two generally different
partitions of the same model, which is the situation the selection step is
written for; no subsequence or compatibility reindexing is needed, since both
come from the same original models.

**Matching.**  Each compressor `q` acts by a permutation approximating it, and
`q Γ q⁻¹ ≤ Γ` means it carries `Γ`-components towards `Γ`-components: by
expansion, apart from components covering `o(|Y|)` vertices, each transported
component lands almost entirely inside a single one.  Distinct transported
components may select the same target, so an *injective* matching is chosen —
this is `LocalCriterion`, and it is the step that a union of expanders would
otherwise defeat.

**Selection.**  For the distinguished compressor, the matching makes every
fixed `Γ`-word preserve the transported components almost everywhere;
conjugating by its inverse transfers that to the `J`-generators, because
`centralizes` says the compressed copy of `Γ` commutes with `J`. One original
component is then selected on which multiplication, commutation and the
`disjoint` distinctness test all hold outside a negligible set
(`SelectionOutput`).

**Repair and conclude.**  Restricting to that component, completing the partial
permutations, discarding a negligible set to restore uniform expansion and
completing again yields a sofic approximation of `Γ × J` on a *single*
expander — a `MatchingCertificate`. The second prerequisite then gives
`IsLEF J`, and the contrapositive is the claim.

## Not a restatement of either prerequisite

The first mentions no second factor and concludes nothing about LEF; the second
is vacuous without a single-expander approximation of a product, which nothing
in the first supplies. The matching and selection between them is where the
compression hypotheses (`compressedEnd_spec`, `centralizes`, `disjoint`) are
consumed, and they appear in neither prerequisite.
