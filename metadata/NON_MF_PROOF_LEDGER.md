# Spectral-compression paper: proof-step ledger

Spec document: `non_mf_groups_exist.tex`. Formal development:
`GroupApproximation/`.

## Audited revision

| | |
| --- | --- |
| commit | spectral-compression rewrite of 2026-08-24 |
| `git hash-object non_mf_groups_exist.tex` | `00cfff9aaf3223664668bc2c9c8a5fd3bc492c19` |
| sha256 of the file | `4bfbfabd040a8adfbc53f8734d96cbbb9bc113de25558d066ec526b1926c95ff` |
| `wc -l` | 378 |

## Status counts

<!-- LEDGER-COUNTS -->
| Column | EXACT | MISMATCH | MISSING | UNDER-SPECIFIED | total |
| --- | --- | --- | --- | --- | --- |
| statement | 8 | 0 | 0 | 0 | 8 |
| proof | 8 | 0 | 0 | 0 | 8 |
<!-- END-LEDGER-COUNTS -->

## Anchors

<!-- LEDGER-ANCHORS -->
| Anchor | Kind | Locator | Digest |
| --- | --- | --- | --- |
| sec:intro | prose | `A countable group is \emph{MF}` | - |
| sec:fd | sec | sec:fd | - |
| sec:spectral | sec | sec:spectral | - |
| sec:geometry | sec | sec:geometry | - |
| sec:quotient | sec | sec:quotient | - |
| sec:a5 | sec | sec:a5 | - |
<!-- END-LEDGER-ANCHORS -->

## Steps

<!-- LEDGER-STEPS -->
| Step | Anchor | Claim | Lean | Stmt | Proof | Obj | Deps | Source | Edit | Note |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| SC.00 | sec:intro | the headline and finite-perfect visible-quotient results | `SpectralPaper.oneInvisibleRelationPackage`; `SpectralPaper.a5UniversalInvisibility`; `FinitePerfectLamp.finitePerfectPackage` | EXACT | EXACT | literal | unconditional | - | YES | closed headline packages, structurally proved later |
| SC.01 | sec:fd | every finite-dimensional representation over every field kills the compression-centralizer defect | `compressionCentralizerDefect_le_ker` | EXACT | EXACT | literal | unconditional | - | YES | finite-dimensional commutant proof |
| SC.02 | sec:spectral | Kazhdan compression collapses commuting corona projections | `ProjectionCompressionCollapse.corona_projection_collapse` | EXACT | EXACT | literal | unconditional | - | YES | printed projection endpoint |
| SC.03 | sec:spectral | clopen spectral projections pass the compression hypotheses and collapse, with zero-dimensional spectrum as the exact endpoint | `SpectralCompression.corona_clopen_projection_collapse`; `SpectralPaper.zeroDimensionalSpectralCollapseTheorem` | EXACT | EXACT | literal | unconditional | - | YES | functional-calculus upgrade |
| SC.04 | sec:spectral | common clopen spectral pieces bound norm motion by the supremum of connected-component diameters | `SpectralComponentMotion.norm_sub_le_of_clopen_projections_eq`; `SpectralPaper.spectralCompressionTheorem` | EXACT | EXACT | literal | unconditional | - | YES | noncommutative reduction, compact topology, and Gelfand duality |
| SC.05 | sec:geometry | the affine doubling datum supplies a residually finite acting group and a Kazhdan compression subgroup | `CommutingLampCollapse.gammaBar_hasKazhdanPropertyT`; `AlternatingLampFamily.vertical_isResiduallyFinite` | EXACT | EXACT | literal | unconditional | BHV; Burger | YES | explicit geometry used by the family theorem |
| SC.06 | sec:quotient | every nontrivial finite perfect lamp has exact visible kernel and universal factorization through the acting group for every advertised unconditional target | `FinitePerfectLamp.finitePerfectPackage`; `SpectralPaper.finitePerfectUniversalInvisibility` | EXACT | EXACT | literal | unconditional | - | YES | exact radicals plus literal universal Hom-bijections |
| SC.07 | sec:a5 | for the $A_5$ lamp the exact kernel is the normal closure of one nontrivial involution and is intrinsically tame | `SpectralPaper.oneInvisibleRelationPackage`; `SpectralPaper.a5UniversalInvisibility`; `SpectralPaper.invisibleKernelTame`; `AlternatingLampLiteral.ker_rightHom_eq_normalClosure_witnessLamp` | EXACT | EXACT | literal | unconditional | - | YES | $A_5$ is the one-relation witness, not the mechanism |
<!-- END-LEDGER-STEPS -->

The compact/Bohr upgrade is deliberately outside the six numbered formal
claims.  Lean reduces it to `PeterWeyl.SeparatesPoints`; the manuscript invokes
the classical Peter--Weyl theorem explicitly in prose.
