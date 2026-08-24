# Spectral-compression paper: proof-step ledger

Spec document: `non_mf_groups_exist.tex`. Formal development:
`GroupApproximation/`.

## Audited revision

| | |
| --- | --- |
| commit | spectral-compression rewrite of 2026-08-24 |
| `git hash-object non_mf_groups_exist.tex` | `af70869fb0d0a19ae81955df4a702132b4410c42` |
| sha256 of the file | `fed635ca55f9e8fe65b8c52a0015e9ed0e3cb0ca13c28208ce2894c2809734d4` |
| `wc -l` | 376 |

## Status counts

<!-- LEDGER-COUNTS -->
| Column | EXACT | MISMATCH | MISSING | UNDER-SPECIFIED | total |
| --- | --- | --- | --- | --- | --- |
| statement | 6 | 0 | 0 | 0 | 6 |
| proof | 6 | 0 | 0 | 0 | 6 |
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
| SC.01 | sec:fd | every finite-dimensional representation over every field kills the compression-centralizer defect | `compressionCentralizerDefect_le_ker` | EXACT | EXACT | literal | unconditional | - | YES | finite-dimensional commutant proof |
| SC.02 | sec:spectral | Kazhdan compression collapses commuting corona projections | `ProjectionCompressionCollapse.corona_projection_collapse` | EXACT | EXACT | literal | unconditional | - | YES | printed projection endpoint |
| SC.03 | sec:spectral | clopen spectral projections pass the compression hypotheses and collapse | `SpectralCompression.corona_clopen_projection_collapse` | EXACT | EXACT | literal | unconditional | - | YES | functional-calculus upgrade |
| SC.04 | sec:spectral | common clopen spectral pieces bound norm motion by connected-component diameter | `SpectralComponentDiameter.norm_sub_le_of_same_clopen_spectral_pieces` | EXACT | EXACT | literal | unconditional | - | YES | compact topology plus Gelfand duality |
| SC.05 | sec:quotient | every nontrivial finite perfect lamp has exact MF, finite-dimensional unitary, finite, and all-fields linear radical equal to the lamp subgroup | `FinitePerfectLamp.finitePerfectPackage` | EXACT | EXACT | literal | unconditional | - | YES | the common visible quotient is the acting group |
| SC.06 | sec:a5 | for the $A_5$ lamp the exact kernel is the normal closure of one nontrivial involution | `AlternatingLampLiteral.ker_rightHom_eq_normalClosure_witnessLamp`; `AlternatingLampFamily.alternatingFamilyPackage` | EXACT | EXACT | literal | unconditional | - | YES | $A_5$ is the one-relation witness, not the mechanism |
<!-- END-LEDGER-STEPS -->

The compact/Bohr upgrade is deliberately outside the six numbered formal
claims.  Lean reduces it to `PeterWeyl.SeparatesPoints`; the manuscript invokes
the classical Peter--Weyl theorem explicitly in prose.
