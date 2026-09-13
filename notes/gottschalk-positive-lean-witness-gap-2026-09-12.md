# Gottschalk-positive Lean witness gap, 2026-09-12

This audit distinguishes the new surjunctivity permanence formalization from
the additional nonsofic witness needed for an unconditional existential theorem.
It records the types of available Lean declarations, not a judgment about the
correctness of the cited research papers.

## Exact missing input

`GroupApproximation.HasSoficCentralizerNormalization Γ` is defined in
[`MFNonsoficDoubleEndpoint.lean`](../GroupApproximation/Sofic/MFNonsoficDoubleEndpoint.lean).
It says that, in every faithful sequential permutation-ultraproduct
representation of the ambient group, its image normalizes the centralizer of
the image of `Γ`.

The actual declaration
`KunThomShulmanDouble.symmetricDouble_not_isSofic` in
[`KunThomShulmanDoubleConstruction.lean`](../GroupApproximation/Sofic/KunThomShulmanDoubleConstruction.lean)
requires both `HasSoficCentralizerNormalization Γ` and `¬ Γ.Normal`.
`KunThomDoubleWitness.conclusion_of_inputs` in
[`KunThomDoubleWitness.lean`](../GroupApproximation/Sofic/KunThomDoubleWitness.lean)
also takes the centralizer property explicitly. Searching the repository's
Lean declarations found no positive theorem producing this property for the
intended Kun–Thom pair. These endpoints therefore cannot currently supply an
unconditional nonsofic double by themselves.

The mathematical literature boundary is Kun–Thom, arXiv:2608.06222, specifically
the Kazhdan/infranormal centralizer theorem and its nonsoficity application.
The repository records that boundary in the declarations above; no new axiom
has been introduced to fill it.

## Concrete pair versus nearby existing examples

The polynomial/Laurent elementary-group pair cited in the research claim has
not been instantiated in the existing Lean witness endpoint. The module
[`ProfiniteClosure.lean`](../GroupApproximation/Sofic/ProfiniteClosure.lean)
explicitly describes that arithmetic instantiation as paper-level, while
formalizing a general separating-quotient criterion.

The nearby `TerminalQuotientPresentation.SigmaGroup` does have a proved
residual-finiteness theorem, `sigmaGroup_residuallyFinite`, in
[`SigmaGroupMF.lean`](../GroupApproximation/Sofic/SigmaGroupMF.lean), and its
subgroup has the proved compression-pair property
`sigmaBase_isCompressionPair` in
[`SigmaCompressionPair.lean`](../GroupApproximation/Sofic/SigmaCompressionPair.lean).
Those declarations do not prove that its symmetric double is nonsofic.

The literal doubling wreath results in
[`LiteralDoublingWreathNonMF.lean`](../GroupApproximation/Sofic/LiteralDoublingWreathNonMF.lean)
prove non-MF statements. They must not be read as nonsoficity statements;
[`SoficNonMFAssembly.lean`](../GroupApproximation/Sofic/SoficNonMFAssembly.lean)
explicitly constructs sofic, non-MF wreath products.

The unconditional nonsofic endpoints in
[`MainResults.lean`](../GroupApproximation/Endpoint/MainResults.lean) concern
Leavitt groups. No identification placing those groups within the new
surjunctivity permanence theorem was found.

## Scope of the centralizer counterexample

[`CentralizerNormalizationRefuted.lean`](../GroupApproximation/Sofic/CentralizerNormalizationRefuted.lean)
proves that `HasSoficCentralizerNormalization` fails for a reflection subgroup
of the dihedral group of order six. Thus the property cannot be discharged
for arbitrary subgroup inclusions. That subgroup is not an infranormal,
nonnormal compression pair, so this counterexample does not refute the
intended Kun–Thom specialization.

## Permitted endpoint and remaining work

An exact conditional endpoint may use an explicit hypothesis
`¬ IsSofic (SymmetricDouble G Γ)`, together with residual finiteness and finite
generation of `G`, to return that same double as a finitely generated,
surjunctive, nonsofic group once double permanence is proved. The nonsoficity
hypothesis must remain visible in its theorem type.

An unconditional existence theorem additionally needs a concrete pair and a
proof term for its nonsoficity. Neither a renamed package of that conclusion,
a non-MF theorem, nor the new surjunctivity theorem supplies the missing proof.
