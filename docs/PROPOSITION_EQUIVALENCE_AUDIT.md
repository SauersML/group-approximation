# Proposition-level equivalence audit: manuscript margin links vs Lean statements

Date: 2026-08-13, at commit 6233ac05.  Method: every `\leanverified`
margin link in `non_mf_groups_exist.tex` was compared, by direct reading,
against the full Lean statement it names, including the definitions the
statement routes through (`NormMatrixCoronaUnitary`, `IsOperatorMF`,
`coronaMFResidual`, `KazhdanCompressionCore`, `compressionCentralizerDefect`).
The question judged is not name plausibility but whether the English
sentence carrying the mark asserts exactly what the Lean proposition
states.

## Definitional pillars

- `NormMatrixCoronaUnitary X = (∀ n, unitaryGroup (X n) ℂ) ⧸
  nullCofiniteOpSubgroup X` is verbatim the manuscript's unitary norm
  corona (eq. `eq:unitary-corona`); the sequence sizes are required
  positive in `IsOperatorMF`.  Its docstring states, matching the
  manuscript's legend footnote, that the C*-quotient and the polar
  isomorphism are not defined in the development (the C*-side algebra is
  under construction in `Analysis/NormMatrixCorona.lean`).
- `IsOperatorMF G` = existence of an injective homomorphism into some
  `NormMatrixCoronaUnitary X` = the manuscript's definition of an MF
  group.  EXACT.
- `coronaMFResidual G` = elements killed by every such homomorphism = the
  manuscript's MF radical as defined over `eq:unitary-corona`.  EXACT.
- `Group.IsFinitelyPresented` is mathlib's classical predicate.

## Verdicts (15 links)

| # | tex site | declaration | verdict |
|---|----------|-------------|---------|
| 1 | existence sentence after Thm A | `ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF` | EXACT: `∃ E, Group E, IsFinitelyPresented E ∧ ¬IsOperatorMF E`; the witness is the internally constructed group, as the legend footnote discloses |
| 2 | Thm B | `compressionCentralizerDefect_le_ker` | EXACT: arbitrary field `k`, `FiniteDimensional k V`, `π : H →* (V ≃ₗ[k] V)`, kills all of `𝔇(H,L)`; the displayed commutator case is the generator instance |
| 3 | Lem `lem:alpha` | `AffineSL3Doubling.doubling_package` | EXACT: injectivity ∧ range characterization (`2•v`) ∧ index 8 ∧ `a ∉ range` |
| 4 | Prop `prop:witness` | `LiteralNonMFLinearWitness.literal_mark_ne_one` | EXACT: `mark ≠ 1` in the literal eight-generator presented group |
| 5 | `sec:findim` corollary | `literal_finiteDimensional_rep_not_injective` | EXACT: no injective `π : MarkedGroup →* (End k V)ˣ`, any field, any finite dimension |
| 6 | Thm `thm:criterion` | `KazhdanCompressionCore.finiteNormal_le_coronaMFResidual` | EXACT: countable `E`, pattern structure, finite normal `F ≤ defectNormal` ⟹ `F ≤ coronaMFResidual` |
| 7 | Thm `thm:normalkazhdan` | `normalKazhdan_le_coronaMFResidual` | EXACT: normal `K` with `HasKazhdanPropertyT K`, `K ≤ defectNormal` ⟹ `K ≤ coronaMFResidual` |
| 8 | Lem `lem:square` | `commutator_conjugate_eq_commutator_sq_of_sq_eq_one` | EXACT |
| 9 | Thm `thm:horn` proof, first half | `ChosenUniversalHorn.isOperatorMF_satisfies_chosenQuasiIdentity` | EXACT: every `IsOperatorMF` group satisfies the chosen quasi-identity; tex phrasing is existential over the chosen presentation |
| 10 | Thm `thm:horn` proof, second half | `markedGroup_not_satisfies_chosenQuasiIdentity` | EXACT: the chosen presented group fails it via the canonical assignment |
| 11 | Lem `lem:faithfultrace` step | `FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one` | EXACT: isometries over matrix amplifications of a faithful-tracial algebra are unitaries |
| 12 | Thm `thm:uniform` | `finiteNormal_uniform_invisibility_positiveModel` | EXACT in quantifier shape: `∀ε>0 ∃δ>0 ∃F₀ finite ∀` finite model `∀φ` with δ-multiplicativity on `F₀` ⟹ conclusion for the marked element |
| 13 | Thm `thm:markedclosed` | `MarkedGroupSpace.isClosed_operatorMFLocus` | EXACT: the MF locus is closed in the fixed-rank marked-group space |
| 14 | Cor `cor:chosencylinder` | `chosenCylinder_isClopen` | EXACT: tex claims a clopen set for *some* finite presentation and word; the Lean witnesses are the chosen ones |
| 15 | Cor `cor:chosencylinder` | `chosenCylinder_subset_nonMF` | EXACT: every marked group in the cylinder is `¬IsOperatorMF` |

## Boundary facts (disclosed in the manuscript's legend footnote)

1. The formal statements range over unitary norm coronas; the passage to
   `U(Q)` is the manuscript's Lemma `lem:unitarycorona` (paper-proved;
   the C*-side formalization is in progress).
2. The unconditional existence witness is the internally constructed
   group, not identified with the displayed group `E`; the corona
   conclusion for `E` itself is established by the paper proof, with the
   Lean side conditional on property (T) of the raw presented base until
   the presentation-completeness program closes it.
