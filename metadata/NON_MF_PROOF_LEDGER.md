# Spectral-compression paper: proof-step ledger

Spec document: `non_mf_groups_exist.tex`. Formal development:
`GroupApproximation/`.

## Audited revision

| | |
| --- | --- |
| commit | spectral-compression rewrite of 2026-08-24 |
| `git hash-object non_mf_groups_exist.tex` | `b4545db9d820a7c63882f0adb3ab7cee800415de` |
| sha256 of the file | `6885172a8839b00c2829f586cf67e1c3737dce5dec4e591d1bcfd5350696d46a` |
| `wc -l` | 376 |

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
| SC.00 | sec:intro | the headline and finite-perfect visible-quotient results | `AlternatingLampFamily.alternatingFamilyPackage`; `AlternatingLampLiteral.ker_rightHom_eq_normalClosure_witnessLamp`; `FinitePerfectLamp.finitePerfectPackage` | EXACT | EXACT | literal | unconditional | - | YES | rhetorical headline, structurally proved later |
| SC.01 | sec:fd | every finite-dimensional representation over every field kills the compression-centralizer defect | `compressionCentralizerDefect_le_ker` | EXACT | EXACT | literal | unconditional | - | YES | finite-dimensional commutant proof |
| SC.02 | sec:spectral | Kazhdan compression collapses commuting corona projections | `ProjectionCompressionCollapse.corona_projection_collapse` | EXACT | EXACT | literal | unconditional | - | YES | printed projection endpoint |
| SC.03 | sec:spectral | clopen spectral projections pass the compression hypotheses and collapse | `SpectralCompression.corona_clopen_projection_collapse` | EXACT | EXACT | literal | unconditional | - | YES | functional-calculus upgrade |
| SC.04 | sec:spectral | common clopen spectral pieces bound norm motion by connected-component diameter | `SpectralComponentDiameter.norm_sub_le_of_same_clopen_spectral_pieces` | EXACT | EXACT | literal | unconditional | - | YES | compact topology plus Gelfand duality |
| SC.05 | sec:geometry | the affine doubling datum supplies a residually finite acting group and a Kazhdan compression subgroup | `CommutingLampCollapse.gammaBar_hasKazhdanPropertyT`; `AlternatingLampFamily.vertical_isResiduallyFinite` | EXACT | EXACT | literal | unconditional | BHV; Burger | YES | explicit geometry used by the family theorem |
| SC.06 | sec:quotient | every nontrivial finite perfect lamp has exact visible kernel and universal factorization through the acting group | `FinitePerfectLamp.finitePerfectPackage`; `FinitePerfectLamp.actualCoronaMFResidual_eq_lampSub`; `comp_mk'_bijective`; `precomp_bijective` | EXACT | EXACT | literal | unconditional | - | YES | the common visible quotient is the acting group |
| SC.07 | sec:a5 | for the $A_5$ lamp the exact kernel is the normal closure of one nontrivial involution | `AlternatingLampLiteral.ker_rightHom_eq_normalClosure_witnessLamp`; `AlternatingLampFamily.alternatingFamilyPackage` | EXACT | EXACT | literal | unconditional | - | YES | $A_5$ is the one-relation witness, not the mechanism |
<!-- END-LEDGER-STEPS -->

The compact/Bohr upgrade is deliberately outside the six numbered formal
claims.  Lean reduces it to `PeterWeyl.SeparatesPoints`; the manuscript invokes
the classical Peter--Weyl theorem explicitly in prose.
