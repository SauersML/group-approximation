import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialEndpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThmMainA.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.ExpanderBridge
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Definitions.SoficPrinted
import GroupApproximation.Leavitt.ElementaryFTwoMatrixProduct
import GroupApproximation.Meta.AxiomGuard
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Theorem `thm:main`: endpoints (M1, G3, T1)

`simple_kazhdan_sofic_group.tex`, Theorem `thm:main` (tex l.69–80):

> Let $X\subseteq A^{\Z}$ be an infinite minimal subshift over a finite alphabet, with shift $T$, and
> let $\LC(X,\F_2)$ be the ring of locally constant functions $X\to\F_2$. Then
> $G_X=\EL_3\bigl(\LC(X,\F_2)\rtimes_T\Z\bigr)$ is an infinite, finitely generated, simple group with
> Kazhdan's property~(T), and an expander limit, in the sense defined below, of finite simple groups
> $\SL_{3N}(\F_2)$. So $G_X$ is locally embeddable into finite groups (LEF), sofic and hyperlinear.

The expander limit is the printed one (tex l.86–100: marked convergence and *vertex* expansion). The
LEF, sofic and hyperlinear notions are those of tex l.102–109.

## Endpoints

* `main : PrintedSimpleKazhdanSoficMain`: the corpus form (every `n ≥ 3`, marked limit and edge
  expansion), from `SimpleKazhdanSofic.printedSimpleKazhdanSoficMain`.
* `main_el`: for every `n ≥ 3`, `EL_n(R)` is an expander limit, in the printed sense of
  `ThmMainA.IsExpanderLimitOfClass`, of the finite simple groups `SL_{nN}(F₂)` (tex l.185–186).
* `main_printed`: tex l.69–80 for `G_X = G S`, with the class `IsFiniteSimpleSLMultiple 3` of finite
  simple groups `SL_{3N}(F₂)`, and the closed bundle `printedMainTheorem`.
* `main_printed_sk01`: the same with Lane 1's printed definitions (`Full.SK01.IsExpanderLimitOfClass`,
  `Full.SK01.IsFiniteSimpleSL3NF2`, `IsLEFPrinted`, `PrintedIsSofic`, `PrintedIsHyperlinear`), and the
  closed bundle `printedMainTheoremSK01`.
* `periodicMatricial`, `periodicMatricial_printed`: periodic approximations make `R` matricial via
  `S = {1, u, u⁻¹} ∪ {e_a}` (tex l.187–192 and sec:main l.357–392).
* `periodicApproximationsRemark` (tex l.191–192): *Periodic approximations of `X` give such maps, and
  Theorem `thm:main` follows.*
* `tabProps_first_rows` (`tab:props`, tex l.197–213): finitely generated, infinite, simple, (T),
  expander limit of `SL_{3N}(F₂)`, LEF, sofic, hyperlinear.

All proofs reuse closed corpus theorems. None of them takes a hypothesis standing in for a
literature result.
-/

namespace GroupApproximation.Full.SK05

open GroupApproximation.SimpleKazhdanSofic
open SymbolicDynamics.FullShift

/-! ## The classes of finite simple groups `SL_{nN}(F₂)` -/

/-- The class of **finite simple groups `SL_{nN}(F₂)`** (tex l.78 for `n = 3`, l.185–186 in general):
finite simple groups isomorphic to the special linear group over `F₂` on a finite index type of size
`n * N` for some `N`. -/
def IsFiniteSimpleSLMultiple (n : ℕ) (Q : Type) [Group Q] : Prop :=
  Finite Q ∧ IsSimpleGroup Q ∧
    ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι), Fintype.card ι = n * N ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup ι (ZMod 2))

/-- A simple `SL_{n × N}(F₂)`, indexed by `Fin n × Fin N`, lies in the class `SL_{nN}(F₂)`. -/
theorem isFiniteSimpleSLMultiple_blocks (n N : ℕ)
    (hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n × Fin N) (ZMod 2))) :
    IsFiniteSimpleSLMultiple n (Matrix.SpecialLinearGroup (Fin n × Fin N) (ZMod 2)) := by
  refine ⟨inferInstance, hsimple, N, Fin n × Fin N, inferInstance, inferInstance, ?_,
    ⟨MulEquiv.refl _⟩⟩
  show Fintype.card (Fin n × Fin N) = n * N
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- `SL_{3 × N}(F₂) ≃* SL_{3N}(F₂)`, through `GL = SL` over `F₂` and reindexing along
`Fin 3 × Fin N ≃ Fin (3 * N)`. -/
noncomputable def slBlocksEquiv (N : ℕ) :
    Matrix.SpecialLinearGroup (Fin 3 × Fin N) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin (3 * N)) (ZMod 2) :=
  (ChainRadical.unitsZModTwoEquivSL (Fin 3 × Fin N)).symm.trans
    ((Units.mapEquiv (Matrix.reindexRingEquiv (ZMod 2) finProdFinEquiv).toMulEquiv).trans
      (ChainRadical.unitsZModTwoEquivSL (Fin (3 * N))))

/-- A simple `SL_{3 × N}(F₂)` lies in Lane 1's printed class `SL_{3N}(F₂)`. -/
theorem isFiniteSimpleSL3NF2_blocks (N : ℕ)
    (hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3 × Fin N) (ZMod 2))) :
    SK01.IsFiniteSimpleSL3NF2 (Matrix.SpecialLinearGroup (Fin 3 × Fin N) (ZMod 2)) :=
  ⟨inferInstance, hsimple, N, ⟨slBlocksEquiv N⟩⟩

/-! ## `thm:main` -/

/-- **Theorem `thm:main`**, corpus form (tex l.69–80, with `n ≥ 3` as in tex l.185–186): marked
limits of `SL_{nN}(F₂)` with edge-expanding Cayley graphs; LEF, sofic, hyperlinear. -/
theorem main : PrintedSimpleKazhdanSoficMain :=
  SimpleKazhdanSofic.printedSimpleKazhdanSoficMain

/-- `EL_n(LC(X, F₂) ⋊_T ℤ)`. -/
abbrev EL (n : ℕ) {A : Type} [TopologicalSpace A] (S : Subshift A ℤ) : Type :=
  ↥(elementaryGroup (Fin n) (SimpleKazhdanSofic.R S))

/-- **Theorem `thm:main` for `EL_n`, `n ≥ 3`** (tex l.69–80 and l.185–186): `EL_n(R)` is infinite,
finitely generated, simple and Kazhdan, an expander limit in the printed sense (tex l.86–100) of the
finite simple groups `SL_{nN}(F₂)`, and LEF, sofic and hyperlinear. -/
theorem main_el (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : SimpleKazhdanSofic.IsMinimal S)
    (n : ℕ) (hn : 3 ≤ n) :
    Infinite (EL n S) ∧ Group.FG (EL n S) ∧ IsSimpleGroup (EL n S) ∧
      HasKazhdanPropertyT.{0, 0} (EL n S) ∧
      ThmMainA.IsExpanderLimitOfClass (IsFiniteSimpleSLMultiple n) (EL n S) ∧
      IsLEF (EL n S) ∧ IsSofic (EL n S) ∧ IsHyperlinear (EL n S) := by
  obtain ⟨hinfG, hfg, hsimple, hT, hlimit, hLEF, hsofic, hhyp⟩ :=
    SimpleKazhdanSofic.printedSimpleKazhdanSoficMain A S hinf hmin n hn
  refine ⟨hinfG, hfg, hsimple, hT, ?_, hLEF, hsofic, hhyp⟩
  obtain ⟨_, _, N, _, hsimpleSL, hlim, hexp⟩ := hlimit
  obtain ⟨m, g, q, hq⟩ := ThmMainA.isExpanderLimit_of_isMarkedLimit hlim hexp
  have hclass : ∀ ℓ, IsFiniteSimpleSLMultiple n
      (Matrix.SpecialLinearGroup (Fin n × Fin (N ℓ)) (ZMod 2)) := fun ℓ =>
    isFiniteSimpleSLMultiple_blocks n (N ℓ) (hsimpleSL ℓ)
  exact ⟨m, g, fun ℓ => Matrix.SpecialLinearGroup (Fin n × Fin (N ℓ)) (ZMod 2),
    fun _ => inferInstance, q, hclass, hq⟩

/-- **Theorem `thm:main`** (tex l.69–80): for an infinite minimal subshift `X` over a finite alphabet,
`G_X = EL₃(LC(X, F₂) ⋊_T ℤ)` is an infinite, finitely generated, simple group with property (T), an
expander limit (tex l.86–100) of finite simple groups `SL_{3N}(F₂)`, and LEF, sofic and hyperlinear. -/
theorem main_printed (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : SimpleKazhdanSofic.IsMinimal S) :
    Infinite (SimpleKazhdanSofic.G S) ∧ Group.FG (SimpleKazhdanSofic.G S) ∧
      IsSimpleGroup (SimpleKazhdanSofic.G S) ∧ HasKazhdanPropertyT.{0, 0} (SimpleKazhdanSofic.G S) ∧
      ThmMainA.IsExpanderLimitOfClass (IsFiniteSimpleSLMultiple 3) (SimpleKazhdanSofic.G S) ∧
      IsLEF (SimpleKazhdanSofic.G S) ∧ IsSofic (SimpleKazhdanSofic.G S) ∧
      IsHyperlinear (SimpleKazhdanSofic.G S) :=
  main_el A S hinf hmin 3 le_rfl

/-- **Theorem `thm:main`** (tex l.69–80) as one closed statement. -/
def PrintedMainTheorem : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → SimpleKazhdanSofic.IsMinimal S →
      Infinite (SimpleKazhdanSofic.G S) ∧ Group.FG (SimpleKazhdanSofic.G S) ∧
        IsSimpleGroup (SimpleKazhdanSofic.G S) ∧
        HasKazhdanPropertyT.{0, 0} (SimpleKazhdanSofic.G S) ∧
        ThmMainA.IsExpanderLimitOfClass (IsFiniteSimpleSLMultiple 3) (SimpleKazhdanSofic.G S) ∧
        IsLEF (SimpleKazhdanSofic.G S) ∧ IsSofic (SimpleKazhdanSofic.G S) ∧
        IsHyperlinear (SimpleKazhdanSofic.G S)

/-- **Theorem `thm:main`**, closed (tex l.69–80). -/
theorem printedMainTheorem : PrintedMainTheorem := by
  intro A _ _ _ S hinf hmin
  exact main_printed A S hinf hmin

/-- **Theorem `thm:main`** (tex l.69–80) with Lane 1's printed definitions: the vertex-expansion
expander limit of `Full.SK01`, the class `SL_{3N}(F₂)` indexed by `Fin (3 * N)`, printed LEF
(tex l.102–104), and printed sofic and hyperlinear (tex l.105–109). -/
theorem main_printed_sk01 (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : SimpleKazhdanSofic.IsMinimal S) :
    Infinite (SimpleKazhdanSofic.G S) ∧ Group.FG (SimpleKazhdanSofic.G S) ∧
      IsSimpleGroup (SimpleKazhdanSofic.G S) ∧ HasKazhdanPropertyT.{0, 0} (SimpleKazhdanSofic.G S) ∧
      SK01.IsExpanderLimitOfClass SK01.IsFiniteSimpleSL3NF2 (SimpleKazhdanSofic.G S) ∧
      SK01.IsLEFPrinted (SimpleKazhdanSofic.G S) ∧ SK01.PrintedIsSofic (SimpleKazhdanSofic.G S) ∧
      SK01.PrintedIsHyperlinear (SimpleKazhdanSofic.G S) := by
  obtain ⟨hinfG, hfg, hsimple, hT, hlimit, hLEF, hsofic, -⟩ :=
    SimpleKazhdanSofic.printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  refine ⟨hinfG, hfg, hsimple, hT, ?_, (SK01.isLEFPrinted_iff_isLEF _).2 hLEF,
    SK01.printedIsSofic_of_isSofic hsofic, SK01.printedIsHyperlinear_of_isSofic hsofic⟩
  obtain ⟨_, _, N, _, hsimpleSL, hlim, hexp⟩ := hlimit
  have hC : ∀ ℓ, SK01.IsFiniteSimpleSL3NF2
      (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)) := fun ℓ =>
    isFiniteSimpleSL3NF2_blocks (N ℓ) (hsimpleSL ℓ)
  exact SK01.isExpanderLimitOfClass_of_markedLimit_expanderFamily hC hlim hexp

/-- **Theorem `thm:main`** (tex l.69–80) with Lane 1's printed definitions, as one closed statement. -/
def PrintedMainTheoremSK01 : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → SimpleKazhdanSofic.IsMinimal S →
      Infinite (SimpleKazhdanSofic.G S) ∧ Group.FG (SimpleKazhdanSofic.G S) ∧
        IsSimpleGroup (SimpleKazhdanSofic.G S) ∧
        HasKazhdanPropertyT.{0, 0} (SimpleKazhdanSofic.G S) ∧
        SK01.IsExpanderLimitOfClass SK01.IsFiniteSimpleSL3NF2 (SimpleKazhdanSofic.G S) ∧
        SK01.IsLEFPrinted (SimpleKazhdanSofic.G S) ∧ SK01.PrintedIsSofic (SimpleKazhdanSofic.G S) ∧
        SK01.PrintedIsHyperlinear (SimpleKazhdanSofic.G S)

/-- **Theorem `thm:main`** with the printed definitions, closed (tex l.69–109). -/
theorem printedMainTheoremSK01 : PrintedMainTheoremSK01 := by
  intro A _ _ _ S hinf hmin
  exact main_printed_sk01 A S hinf hmin

/-! ## Periodic approximations -/

/-- **Periodic approximations make `R` matricial** (tex l.187–192, sec:main l.357–392), closed. -/
theorem periodicMatricial : PrintedPeriodicMatricialStatement :=
  SimpleKazhdanSofic.printedPeriodicMatricialStatement

/-- **Periodic approximations** (tex l.187–192, l.357–392): for an infinite minimal subshift there are
`N_k ≥ 1` and maps `φ_k : R → M_{N_k}(F₂)` with `φ_k(1) = I`, `φ_k(S)` generating `M_{N_k}(F₂)` for
`S = {1, u, u⁻¹} ∪ {e_a}`, and eventually additive and multiplicative on each pair. -/
theorem periodicMatricial_printed (A : Type) [TopologicalSpace A] [DiscreteTopology A]
    [DecidableEq A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) :
    ∃ (N : ℕ → ℕ) (φ : ∀ k, SimpleKazhdanSofic.R S → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
      IsMatricialVia (printedGenerators S) N φ :=
  SimpleKazhdanSofic.printedPeriodicMatricialStatement A S hinf hmin

/-- **tex l.191–192.** *Periodic approximations of `X` give such maps, and Theorem `thm:main`
follows*: both the periodic approximation and `thm:main` hold. -/
theorem periodicApproximationsRemark :
    PrintedPeriodicMatricialStatement ∧ PrintedMainTheorem :=
  ⟨periodicMatricial, printedMainTheorem⟩

/-! ## `tab:props`, first rows -/

/-- **`tab:props`** (tex l.197–213), rows *finitely generated*, *infinite*, *simple*,
*property (T)*, *expander limit of `SL_{3N}(F₂)`*, *LEF, sofic, hyperlinear*, with the printed
definitions of tex l.86–109. -/
def PrintedTabPropsFirstRows : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → SimpleKazhdanSofic.IsMinimal S →
      Group.FG (SimpleKazhdanSofic.G S) ∧ Infinite (SimpleKazhdanSofic.G S) ∧
        IsSimpleGroup (SimpleKazhdanSofic.G S) ∧
        HasKazhdanPropertyT.{0, 0} (SimpleKazhdanSofic.G S) ∧
        SK01.IsExpanderLimitOfClass SK01.IsFiniteSimpleSL3NF2 (SimpleKazhdanSofic.G S) ∧
        IsTextbookLEF (SimpleKazhdanSofic.G S) ∧ SK01.PrintedIsSofic (SimpleKazhdanSofic.G S) ∧
        SK01.PrintedIsHyperlinear (SimpleKazhdanSofic.G S)

/-- **`tab:props`, first rows** (tex l.197–213), closed. -/
theorem tabProps_first_rows : PrintedTabPropsFirstRows := by
  intro A _ _ _ S hinf hmin
  obtain ⟨hinfG, hfg, hsimple, hT, hlim, hLEF, hsofic, hhyp⟩ := main_printed_sk01 A S hinf hmin
  have htext : IsTextbookLEF (SimpleKazhdanSofic.G S) :=
    (isLEF_iff_textbook _).1 ((SK01.isLEFPrinted_iff_isLEF _).1 hLEF)
  exact ⟨hfg, hinfG, hsimple, hT, hlim, htext, hsofic, hhyp⟩

end GroupApproximation.Full.SK05

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.Full.SK05.main
#audit_axioms GroupApproximation.Full.SK05.isFiniteSimpleSLMultiple_blocks
#audit_axioms GroupApproximation.Full.SK05.isFiniteSimpleSL3NF2_blocks
#audit_axioms GroupApproximation.Full.SK05.main_el
#audit_axioms GroupApproximation.Full.SK05.main_printed
#audit_closed_axioms GroupApproximation.Full.SK05.printedMainTheorem
#audit_axioms GroupApproximation.Full.SK05.main_printed_sk01
#audit_closed_axioms GroupApproximation.Full.SK05.printedMainTheoremSK01
#audit_closed_axioms GroupApproximation.Full.SK05.periodicMatricial
#audit_axioms GroupApproximation.Full.SK05.periodicMatricial_printed
#audit_closed_axioms GroupApproximation.Full.SK05.periodicApproximationsRemark
#audit_closed_axioms GroupApproximation.Full.SK05.tabProps_first_rows
