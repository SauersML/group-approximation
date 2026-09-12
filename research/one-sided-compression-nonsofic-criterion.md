---
rg: 2
id: one-sided-compression-nonsofic-criterion
kind: claim
title: The one-sided compression criterion - a non-LEF witness inside a compressed Kazhdan pair forbids soficity
distinct_from:
  kun-expander-decomposition-formalized: That is the first external input, producing a union of expanders from property (T); this is the criterion built on top of it, and its content is the selection of a single component.
  kun-thom-expander-centralizer-formalized: That is the second external input and needs one expander handed to it; this is what hands it one, from data that property (T) alone supplies.
  universal-leavitt-el4-nonsofic: That is one instantiation of this criterion, with an explicit Leavitt group; this is the criterion itself, quantified over every compression setup.
  nonsofic-mechanism-mf-classification: That asks which MF properties the groups produced by this mechanism have, taking their nonsoficity as given; this is the mechanism, and it says nothing about MF.
artifacts:
  - GroupApproximation/Criterion/CompressionSetup.lean
  - GroupApproximation/Criterion/CriterionAssembly.lean
  - GroupApproximation/Criterion/LocalCriterion.lean
  - GroupApproximation/Criterion/SelectionOutput.lean
  - GroupApproximation/Criterion/Scheme.lean
---

ESTABLISHED.  `Criterion/CriterionAssembly.not_isSofic_of_not_isLEF`: given a
`CompressionSetup G Γ J` with property `(T)` for the ambient `G` and for the
compressed subgroup `Γ`, if `J` is not LEF then `G` is not sofic.

A `CompressionSetup` is the data the argument actually consumes, and it is
worth reading as a list because it is what an instantiation must supply:
injections `J ↪ Γ ↪ G`; finite symmetric generating sets for `Γ` and `J`;
`Γ` infinite; a finite set of *compressors* in `G` with a distinguished one,
each conjugating `Γ` into itself (`compressedEnd_spec`:
`embedΓ (compressedEnd q g) = q · embedΓ g · q⁻¹`); `Γ` together with the
compressors generating `G`; the compressed copy of `Γ` centralizing `J`; and
the two copies meeting trivially.

`isLEF_of_ambientDecomposition` is the sharper form: property `(T)` of the
*ambient* group is not consumed as such -- only the expander decomposition it
produces -- so the criterion is stated asking for that decomposition directly,
and `exists_localCriterionData` specializes it.  Property `(T)` of `Γ` is used
twice, for its own decomposition and for the Kazhdan pair the Kun--Thom step
needs.

## What the criterion adds to its two inputs

Exactly the step neither input performs: passing from *many* expanding
components to *one*.  `LocalCriterion` and `SelectionOutput` do it — the
compressors transport `Γ`-components into `Γ`-components, an injective
matching is chosen so that a fixed `Γ`-word preserves the transported
components almost everywhere, one component is selected on which the
multiplication, commutation and distinctness tests all hold outside a
negligible set, and the restricted action is completed and repaired back to an
exact expander.  That output is a `MatchingCertificate`, which is precisely
what [[kun-thom-expander-centralizer-formalized]] consumes.

This is the mechanism behind every nonsoficity result in the development, and
the reason those results are not independent of Kun and Kun--Thom: the two of
them are the endpoints of the argument, and this is the bridge.
