# Lane chain-radical: thm:core-mf-radical (tex 1539–1590) and Introduction 249–258

Snapshot: origin/main 73a84cd9c (09-13).  Item S6b of `notes/nm-swarm/reports/chain-core.md`.
Census: 0 rows.  All modules below land unwired; wiring goes to the wire queue after a green probe.

## Existing carriers (origin/main, grepped for uses)

| use | carrier | module |
|---|---|---|
| `EL_n(R)`, roots, Steinberg commutator, two-step roots | `elementaryGroup`, `elementaryUnit`, `elementaryUnit_commutator`, `elementaryUnit_mem_of_two_step` | Leavitt/ElementaryGroup |
| `EL_n(f)` and its surjectivity | `elementaryGroupMap`, `elementaryGroupMap_surjective_of_surjective` | Leavitt/ElementaryGroup |
| block flattening `EL_ι(M_κ R) ≅ EL_{ι×κ}(R)` | `elementaryBlockUnitEquiv(_single)`, `elementaryBlockGroup_map`, `elementaryBlockEquiv` | Leavitt/ElementaryGroup |
| `EL_n(R, I)`, root addition into a normal subgroup | `relativeElementary`, `normalLevel`, `relativeElementary_normalLevel_le` | Leavitt/CongruenceSubgroups |
| determinant one ⇒ elementary over a field | `AlgebraicK.mem_elementaryGroup_of_detUnits_eq_one` | KOne/FieldKOneDeterminant |
| prop:torsion-defect-ring clause 1 | `manuscriptTorsionComplementaryIdempotents` (closed, audited) | Manuscript/OneSidedMFRadical/TorsionComplementaryIdempotents |
| MF radical | `MFQuotientUnits.mfHomKernel`, `mem_mfHomKernel_iff` | Manuscript/OneSidedMFRadical/MFHomKernel |
| LEF rings, EL over LEF, countable LEF ⇒ MF | `IsLEFRing`, `IsLEFRing.matrix`, `isLEF_units`, `isLEF_elementaryGroup`, `isOperatorMF_of_isLEF` | Pestov91/LEF, Sofic/LocallyFiniteMF |
| locally finite group | `IsLocallyFiniteGroup` | Sofic/LocallyFiniteMF |

## Planned modules (dependency order)

1. `GroupApproximation/Leavitt/ElementaryFTwoMatrixProduct.lean`: definitions and G1, with no upstream dependency.
   `ChainRadical.MatrixProductFTwo m h := ∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) (ZMod 2)`;
   `zmodTwo_units_eq_one`, `elementaryGroup_zmodTwo_eq_top [Nonempty κ]`,
   `elementaryGroup_matrix_zmodTwo_eq_top [Nontrivial ι]` (block flattening),
   `elementaryGroup_pi_eq_top` (finite products), `elementaryGroup_matrixProductFTwo_eq_top`.
2. `GroupApproximation/Leavitt/CornerUnitHom.lean`: `g = (1−p)I_n + h`, with no upstream dependency.
   For `φ : A →ₙ+* R`: `cornerMatrixHom φ : Matrix ι ι A →* Matrix ι ι R` (`M ↦ scalar (1 − φ 1) + M.map φ`),
   `cornerUnitHom`, `cornerUnitHom_elementaryUnit` (root ↦ root with coefficient `φ a`),
   `cornerMatrixHom_injective`, `exists_cornerUnitHom_eq` (entries of `g − 1`, `g⁻¹ − 1` in `range φ`).
3. `GroupApproximation/Leavitt/LocallyMatricialCongruenceKernel.lean`: identify the kernel, and show it is locally finite.
   The local-matriciality hypothesis is an inline binder of the shape proposed below; it is not a new definition.
   `mem_closure_rootsIn_of_mem_ker`, `ker_elementaryGroupMap_eq_relativeElementary`,
   `ker_unitsMapMatrix_le_elementaryGroup`, `isLocallyFiniteGroup_ker_unitsMapMatrix`.
4. `GroupApproximation/Manuscript/OneSidedMFRadical/TorsionDefectIdealRadical.lean`: the lower bound.
   `mfHomKernel_le_ker` (an MF target kills the radical),
   `relativeElementary_span_le_mfHomKernel` (defects `1 − st` with `ts = 1` and finite additive order, `R` countable,
   `n ≥ 4`) via clause 1 + `normalLevel`.
5. `GroupApproximation/Manuscript/ChainCore/MFRadicalRestriction.lean`: generic assembly for a surjection `ρ : R →+* S`
   onto an LEF ring whose kernel is spanned by torsion defects and is locally matricial over `F_2`.
   `GenericMFRadicalRestriction : Prop` + theorem: `Rad(EL_n R) = ker EL_n(ρ) = EL_n(R, ker ρ)`, kernel
   locally finite, `EL_n(ρ)` surjective, `EL_n(S)` LEF; `Rad(GL_n R) = ker GL_n(ρ)`, `GL_n R ⧸ Rad ≃* range`,
   range MF; `EL_n R` (resp. `GL_n R`) MF ⇔ `ker ρ = ⊥`, and then LEF.
6. `GroupApproximation/Manuscript/ChainCore/CoreMFRadical.lean`: `PrintedCoreMFRadical` over `(X, T)`, composing 5 with the
   S1/S4/S5 carriers.  Named residual Props stand in until their owners land.

## Interfaces needed (owner)

- chain-core (S1): `R_X` (SkewMonoidAlgebra over the LC synonym) and its name; `Countable R_X`;
  the defect pair for clopen `P ⊇ T(P)`: `t * s = 1`, `s * t = 1 − d`, `2 • d = 0`.
- chain-matricial (S5): the restriction hom `R_X →+* R_Y`, its surjectivity, and
  `TwoSidedIdeal.ker restriction = TwoSidedIdeal.span {defects}`.  Local matriciality in the shape
  `∀ F : Finset R, (∀ x ∈ F, x ∈ I) → ∃ (m : ℕ) (h : Fin m → ℕ)
     (φ : (∀ a : Fin m, Matrix (Fin (h a)) (Fin (h a)) (ZMod 2)) →ₙ+* R),
     Function.Injective φ ∧ (∀ y, φ y ∈ I) ∧ ∀ x ∈ F, ∃ y, φ y = x`,
  and `ker restriction = ⊥ ↔ CR(T) = univ`.
- chain-itinerary (S4): `IsLEFRing R_Y`.
- chain-reflection (S6a): carries Introduction key `350e53c0b888` (universal directly finite quotient).

## Residual Props (until owners land)

`RXCountable`, `DefectPairTorsion` (chain-core); `RestrictionSurjective`, `RestrictionKernelSpanDefects`,
`RestrictionKernelLocallyMatricialFTwo`, `RestrictionKernelBotIffChainRecurrent` (chain-matricial);
`RYIsLEFRing` (chain-itinerary).  Each is model-tested before it is consumed.

## Key map (WORKLIST keys → planned carrier)

| key | sentence | carrier |
|---|---|---|
| `71da342a2cec` | k = F_2, n ≥ 4 | 6: endpoint binders |
| `ffcebac26044` | Rad = ker = EL_n(R_X, I) | 5 (EL clauses) |
| `1dcedf0a7a5c` | kernel locally finite, surjective, LEF quotient | 3, 5 |
| `87cd8b50757e` | GL_n radical, maximal MF quotient | 5 (GL clauses) |
| `380bfb5990c5` | proposition kills roots in `R d R` | 4 |
| `5ab74e7c4576` | ideals generate I, root addition | 4 |
| `3a5ab131efde` | identify the kernel | 3 |
| `3b9dae111508` | entries in B with local identity p | 2 `exists_cornerUnitHom_eq` |
| `be106727feb1` | g = (1−p)I_n + h | 2 |
| `4c62dd1963db` | n ≥ 2: GL_n(B) = EL_n(B) | 1 |
| `fd54e2645afe` | determinant one over F_2 | 1 `zmodTwo_units_eq_one` |
| `2416b0e3e06b` | block flattening | 1 `elementaryGroup_matrix_zmodTwo_eq_top` |
| `8ffeafc81808` | g generated by roots in I | 3 |
| `c13ca7c28028` | EL and GL kernels equal EL_n(R_X, I) | 3 |
| `a47d16c7fbe5` | local finiteness | 3 |
| `0b84b12a0927` | surjective | 5 + `elementaryGroupMap_surjective_of_surjective` |
| `aef6776a7348` | target LEF hence MF | 4, 5 |
| `5bdc96184b03` | GL_n restriction | 5 |
| `d6d4c3f1cdb5` | MF iff chain recurrent, then LEF | 5, 6 |
| `d2d559dae75f` | finite fields / F_2 | 6 (with S6a) |
| `8ada929ece30` | no fg or (T) | 6: endpoint binder list |
| `684721560ced` `aac4a95b387b` `c6f8fb6abe29` | Introduction: radical = kernel, locally finite, LEF quotient | 6 |
| `d1c3c7f0f3a9` | Introduction: R_X | chain-core S1 |
| `350e53c0b888` | Introduction: universal DF quotient | chain-reflection S6a |

## Infra

No `$NM/lanes/chain-radical.clone`; requested from main.  Modules 1, 2 and 4 are being authored meanwhile.

## Progress log

- 09-13: plan landed (this file).
