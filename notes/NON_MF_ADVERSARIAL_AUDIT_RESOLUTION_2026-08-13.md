# Resolution of the adversarial non-MF audit

This file records which findings from the 13 August 2026 audit were repaired
and which mathematical boundaries remain open.  It is intentionally stricter
than a list of files that happen to compile.

## Specification and object identity

- The literal eight-generator group now has a kernel-checked MF obstruction.
  `LiteralNonMFEndpoint.manuscriptTheoremA` is the exact hypothesis-free
  endpoint, assembled in `LiteralNonMFEndpoint` from the exact P13
  certificate, Kazhdan pinning, finite-normal annihilation, and the Clifford
  witness.
- `ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF` is retained
  only as an independent existential theorem and is labeled `other witness`.
  It is not an object-level certification of Theorem A.
- The literal presentation, literal marked word, nontriviality witness, and
  all-fields finite-dimensional obstruction remain separately formalized.
- `LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT_of_p13` combines the
  checked P13 rotation quotient with the intrinsic affine bridge.  The staged
  rational Hodge certificate supplies property `(T)` of P13, so no
  object-identity premise remains.

## MF terminology and C-star targets

- The manuscript uses **MF** for the CDE group property studied here.  It
  distinguishes this from the stronger reduced-norm convention and from
  purely MF (PMF), where genuine finite-dimensional representations strongly
  converge to the left regular representation.  It does not call these
  mutually equivalent definitions.
- The formal API records the valid implications from the stronger variants
  to CDE-MF, and the text cites Shulman, Schafhauser, and the
  strong-convergence literature with that scope.
- `IsCDEOperatorMF` includes the countability typeclass and strictly
  increasing positive dimensions.  `IsOperatorMF` remains the unrestricted
  internal coordinate predicate; their equivalence for countable groups is a
  theorem, not a definitional identification.
- `NormMatrixCStarCorona` is a genuine C-star quotient, and
  `normMatrixCoronaUnitaryEquiv` is the formal polar-correction equivalence
  between its unitary group and the exact-unitary coordinate quotient.
- The manuscript now says that this identifies the two target models; it does
  not identify group CDE-MF with MF-ness of the reduced group C-star algebra.
- The algebra predicate was corrected to the Blackadar--Kirchberg convention:
  `IsMFAlgebra A` includes separability and a faithful possibly nonunital
  C-star embedding.  `HasMFEmbedding A` is the separate bare embedding
  property.  The unitary restriction of a nonunital embedding is corrected in
  the complementary corner instead of assuming preservation of the unit.

## Proof exposition

- The coordinate-corner proof now says explicitly that polar correction is
  used on the eventually invertible tail and assigns arbitrary unitaries only
  at the finitely many exceptional indices.
- The finite-stage compressor proof now displays the spectral-cut budget, the
  equal-rank reverse-leakage estimate, and the dimension-free `8/64/64` vector
  chain with an explicit epsilon allocation.  Those constants are the ones
  used in `MarkedCompressionSequentialKill.lean`.
- The cyclic comparison is described as the same marked-compression pattern,
  not the same presentation.
- The prose identifies the elementary step narrowly as the equal-rank
  projection reversal, not the entire Kazhdan argument.

## Certification metadata

- Manuscript badges have six disjoint statuses: `exact`, `equiv`, `support`,
  `conditional`, `partial`, and `other witness`.  Only `exact` counts as strict
  object-level certification.
- `scripts/check_non_mf_refs.py` validates the status, module, declaration,
  and generated declaration roster.  It no longer calls a hand-written
  whitelist an exact semantic contract.
- Package declarations, definitions, and proof ingredients are labeled
  `support`; proved target-model equivalences are labeled `equiv`; effective
  consequences that still require a supplied transformation are labeled
  `conditional`.
- Theorem D is now a single zero-input declaration combining separability,
  the canonical faithful trace, stable finiteness of every finite matrix
  amplification, and failure of MF for the literal reduced group C-star
  algebra.  Its badge points directly to that declaration.

## Effectivity and external constructions

- Adian--Rabin recognition and non-r.e. conclusions are formalized only as
  consequences of an explicit computable reduction structure and are labeled
  conditional.  No effective presentation transformation is postulated.
- Scaling, universal-envelope, simple-envelope, and other externally supplied
  construction outputs are labeled supporting or conditional according to
  their actual theorem types.
- The torsion-free full-radical development uses proof-carrying structures for
  the Fournier--Facio/Hull outputs.  Its exact external existence boundary is
  listed in `TORSION_FREE_FULL_CDE_MF_FORMALIZATION.md`.

## Remaining work that is not being mislabeled as complete

1. Formalize the Fournier--Facio/Hull acylindrical small-cancellation existence
   theorems before asserting the torsion-free main theorem unconditionally in
   Lean.
2. A future single-source generator for the long TeX and Lean relator lists
   would reduce transcription risk.  The current release instead keeps the
   literal relator proof package and does not claim generated identity.
3. Reproducible release artifacts should include a clean remote build log,
   axiom audit, source commit, and archive checksum.  These are release-process
   tasks, not mathematical theorems.
