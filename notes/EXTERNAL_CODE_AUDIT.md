# External Lean code audit (physlib / LeanQuantum / Lean-QuantumInfo)

Date: 2026-08-12.  Auditor: W7 mining workstream.  Constraint set by the
user: no lake dependency outside Mathlib, no wholesale vendoring; individual
lemmas only, ported into `GroupApproximation/ForMathlib/` with Apache-2.0
attribution.

Audited commit: `leanprover-community/physlib` @
`c6e61dce0a80e9b1139af2d81cac4dac886c4c29` (shallow clone, 2026-08-12;
Apache-2.0, toolchain 4.32.0 vs our 4.32.2).  Secondary: inQWIRE/LeanQuantum
(v4.26 toolchain), Timeroot/Lean-QuantumInfo (frozen; merged into physlib
2026-03).

## Outcome: ZERO ports.  Nothing passed the porting bar.

The bar was: (a) not already available in this repo or Mathlib in usable
form, AND (b) consumed by live or imminent code, AND (c) porting deletes or
prevents ≥ 3x its length in our code.  Every target failed at least one
prong, for one of two structural reasons:

1. **Our quantitative layer is strictly stronger where it overlaps.**
   Physlib's projection/spectral API (`HermitianMat/Proj.lean`, `CFC.lean`)
   is *qualitative*: it builds projectors, kernels, supports, and CFC
   cutoffs, but contains not a single operator-norm perturbation bound
   (`Proj.lean` has zero occurrences of `‖`).  The non-MF argument lives
   entirely in the perturbative regime (`spectralAbove` calculus,
   `norm_sub_one_mul_spectralAbove_le`, `SpectralCapture`,
   `KazhdanCornerPolar`, `ProjectionRankFlip.norm_one_sub_mul_flip`,
   `rank_unitary_conj`) — all already kernel-checked here.

2. **The rest is welded to their bundled types.**  `trace_projector`,
   `projector_add_orthogonal`, `supportProj`/`kerProj`, `cfc_conj_unitary`,
   the real-valued `HermitianMat.trace` API and the Schatten development all
   live on the bundled `HermitianMat` structure plus their CFC plumbing.
   Extracting "one lemma" drags the type, its order/algebra instances, and
   the CFC bridge — vendoring-scale coupling, which the constraint forbids
   and which the repo does not need.

## Per-target table

| Target | physlib location | Our equivalent | Action |
| --- | --- | --- | --- |
| trace of projector = dim | `HermitianMat/Proj.lean:82` `trace_projector` | rank-based route: `ProjectionRankFlip.rank_unitary_conj` + flip chain (no trace needed) | skipped — have better |
| `P + P⊥ = 1` | `Proj.lean:56` | `spectralBelow := 1 − spectralAbove` (definitional), `one_sub_isOrthogonalProjection` | skipped — have |
| pos/neg spectral projection | `Proj.lean:215–263` (`projLE/projLT` via CFC) | `spectralAbove/Below`, `ApproxInvolutionCorner.positiveProjection/negativeProjection/roundedInvolution` (with quantitative rounding) | skipped — have better |
| spectral projection perturbation bound | **absent in physlib** | `KazhdanCornerPolar`, `SpectralCapture`, `InvolutionRounding` layer | n/a — we are ahead |
| unitary conj preserves trace/eigenvalues | `CFC.lean:208` `cfc_conj_unitary`, `Matrix.lean:97` `sum_eigenvalues_eq_trace` | `rank_unitary_conj`; HS invariances in `MarkedCompressionVectorChain.vecMass_unitary_mulVec`, `vecMass_rowVec_unitary`; trace cyclicity from Mathlib | skipped — have |
| Schatten p = 2 identities | `Schatten.lean` | `NormTraceGap.hsDistSq` family + `UnitaryProjectionBalance` | skipped — have (p = 2 only, which is all the proof uses) |
| general Schatten p | `Schatten.lean:26–289` | none | pointer recorded — relevant only to a FUTURE Schatten-p generalization of the non-MF obstruction; revisit then |
| Pauli X/Z anticommutation | LeanQuantum gates; QECLean | `CliffordLampGroup` (arbitrary index type, unconditional `sign_ne_one`) — strictly stronger than a 2×2 witness | skipped — have better |
| Kronecker/tensor conj identities | `HermitianMat/Unitary.lean` | not consumed anywhere in the live chain | skipped — not needed |

## Conceptual note kept

One physlib design idea is worth stealing *conceptually* (no code): bundling
Hermitian matrices as a type instead of threading `hH : H.IsHermitian`
everywhere.  Not applied retroactively; optional for future new files.

## License compliance

No code was copied, so no attribution obligations were incurred.  If a
future port happens, the scheme fixed here applies: per-block header with
source repo, file path, commit hash, Apache-2.0 notice, and a list of
modifications, placed in `GroupApproximation/ForMathlib/`.

## Search negatives (recorded for future reference)

No external Lean 4 library was found for HNN extensions beyond Mathlib's,
Bass–Serre theory, group MF, operator ultraproducts, or property (T).  For
those, this repository remains ahead of everything surveyed.
