import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.Expanders
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitTransport
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThmMainA.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.PartA
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:general(b)`: the finite simple models `SL_{nN_k}(F₂)`

Manuscript: `simple_kazhdan_sofic_group.tex`, Theorem `thm:general`(b) (tex l.178–186) and the
subsection "Finite simple models" (tex l.316–342).

The files `MarkedLimit.lean` and `Expanders.lean` of this lane prove that `EL_n(R)`, marked by the
`e_ij(s)` (`s ∈ S`), is the marked limit of `EL_n(M_{N_k}(F₂))` marked by the `e_ij(φ_k(s))`, and that
these marked finite groups form an expander family. Here we transport both along the block
flattening `EL_n(M_{N_k}(F₂)) ≃* SL_{n × N_k}(F₂)` (tex l.321–324), whose image of `e_ij(φ_k(s))` is
the block flattened matrix (`coe_slMarking`), prove these finite groups simple, and state the
printed conclusion: an expander limit (vertex-boundary definition, tex l.92–100) of the finite simple
groups `SL_{nN_k}(F₂)`.

* `thm_general_b`: for any ring `R` with `EL_n(R)` infinite and simple.
* `thm_general_b_printed`: the printed setting `R = LC(C, F₂) ⋊ Λ`, with infinitude and simplicity
  from part (a) (`Full.SK03.printedGeneralPartA`).

The hypothesis `0 < N k` is implicit in the text: for `N_k = 0` the ring `M_0(F₂)` is zero, the zero
map satisfies every printed condition on `φ_k`, and `SL_0(F₂)` is trivial, hence neither simple nor a
model in which `e_12(I) ≠ I` (tex l.334–335).
-/

namespace GroupApproximation.Full.SK04

open Filter

/-! ## The block flattening on matrices -/

/-- The identification `GL_ι(F₂) ≃* SL_ι(F₂)` does not change the matrix. -/
theorem coe_unitsEquivSLZModTwo_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι (ZMod 2))ˣ) :
    ((SimpleKazhdanSofic.unitsEquivSLZModTwo ι u : Matrix.SpecialLinearGroup ι (ZMod 2)) :
      Matrix ι ι (ZMod 2)) = (u : Matrix ι ι (ZMod 2)) := by
  have h := MulEquiv.ofBijective_apply_symm_apply (n := u)
    (Matrix.SpecialLinearGroup.toGL (n := ι) (R := ZMod 2))
    ⟨Matrix.SpecialLinearGroup.toGL_injective,
      fun v => ⟨⟨(v : Matrix ι ι (ZMod 2)), SimpleKazhdanSofic.det_units_zmodTwo' v⟩, Units.ext rfl⟩⟩
  exact congrArg Units.val h

/-- **The block flattening** `EL_n(M_N(F₂)) ≃* SL_{n × N}(F₂)` sends a matrix of `N × N` blocks to the
flattened `nN × nN` matrix (tex l.321–324). -/
theorem coe_elementaryBlockEquivSL_apply (n : ℕ) (hn : 3 ≤ n) (N : ℕ) (hN : 0 < N)
    (g : ↥(elementaryGroup (Fin n) (Matrix (Fin N) (Fin N) (ZMod 2)))) :
    ((SimpleKazhdanSofic.elementaryBlockEquivSL n hn N hN g :
        Matrix.SpecialLinearGroup (Fin n × Fin N) (ZMod 2)) :
      Matrix (Fin n × Fin N) (Fin n × Fin N) (ZMod 2)) =
      Matrix.comp (Fin n) (Fin n) (Fin N) (Fin N) (ZMod 2)
        ((g : (Matrix (Fin n) (Fin n) (Matrix (Fin N) (Fin N) (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (Matrix (Fin N) (Fin N) (ZMod 2))) := by
  show ((SimpleKazhdanSofic.unitsEquivSLZModTwo (Fin n × Fin N)
      (SimpleKazhdanSofic.elementaryBlockEquivUnits n hn N hN g) :
        Matrix.SpecialLinearGroup (Fin n × Fin N) (ZMod 2)) :
      Matrix (Fin n × Fin N) (Fin n × Fin N) (ZMod 2)) = _
  rw [coe_unitsEquivSLZModTwo_apply]
  rfl

/-! ## The marked finite simple groups `SL_{nN_k}(F₂)` -/

/-- **The printed models** (tex l.184–186): `SL_{n × N_k}(F₂)` marked by the (block flattened)
transvections `e_ij(φ_k(s))`, `s ∈ S`. -/
noncomputable def slMarking {R : Type*} [Ring R] (n : ℕ) (hn : 3 ≤ n) (S : Finset R) (N : ℕ → ℕ)
    (hN : ∀ k, 0 < N k) (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) (k : ℕ) :
    MarkingIndex n S → Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2) :=
  fun p => SimpleKazhdanSofic.elementaryBlockEquivSL n hn (N k) (hN k) (matricialMarking n S N φ k p)

/-- The marking generator `e_ij(φ_k(s))` of `SL_{n × N_k}(F₂)` is the block flattening of the
elementary matrix `1 + E_ij(φ_k(s))` over `M_{N_k}(F₂)`. -/
theorem coe_slMarking {R : Type*} [Ring R] (n : ℕ) (hn : 3 ≤ n) (S : Finset R) (N : ℕ → ℕ)
    (hN : ∀ k, 0 < N k) (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) (k : ℕ)
    (p : MarkingIndex n S) :
    ((slMarking n hn S N hN φ k p : Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2)) :
      Matrix (Fin n × Fin (N k)) (Fin n × Fin (N k)) (ZMod 2)) =
      Matrix.comp (Fin n) (Fin n) (Fin (N k)) (Fin (N k)) (ZMod 2)
        ((elementaryUnit p.1.1.1 p.1.1.2 p.1.2 (φ k (p.2 : R)) :
            (Matrix (Fin n) (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)))ˣ) :
          Matrix (Fin n) (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) :=
  coe_elementaryBlockEquivSL_apply n hn (N k) (hN k) (matricialMarking n S N φ k p)

/-- `SL_{n × N}(F₂)` is simple for `n ≥ 3`, `N ≥ 1` (tex l.321–324). -/
theorem isSimpleGroup_sl (n : ℕ) (hn : 3 ≤ n) (N : ℕ) (hN : 0 < N) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n × Fin N) (ZMod 2)) := by
  haveI := SimpleKazhdanSofic.isSimpleGroup_elementaryBlock n hn N hN
  haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin n × Fin N) (ZMod 2)) :=
    (SimpleKazhdanSofic.elementaryBlockEquivSL n hn N hN).symm.injective.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective
    (SimpleKazhdanSofic.elementaryBlockEquivSL n hn N hN).toMonoidHom
    (SimpleKazhdanSofic.elementaryBlockEquivSL n hn N hN).surjective

/-- The marked models converge to `EL_n(R)` marked by the `e_ij(s)` (tex l.325–337). -/
theorem isMarkedLimit_slMarking {R : Type*} [Ring R] (n : ℕ) (hn : 3 ≤ n)
    [IsSimpleGroup (elementaryGroup (Fin n) R)]
    (S : Finset R) (hS1 : (1 : R) ∈ S) (hS : Subring.closure (S : Set R) = ⊤)
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) (hφ : IsPrintedMatricial S N φ) :
    SimpleKazhdanSofic.IsMarkedLimit (elementaryMarking n S) (slMarking n hn S N hN φ) := by
  have h := SimpleKazhdanSofic.IsMarkedLimit.map_target
    (H' := fun k => Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2))
    (isMarkedLimit_matricial n hn S hS1 hS N hN φ hφ)
    (fun k => SimpleKazhdanSofic.elementaryBlockEquivSL n hn (N k) (hN k))
  exact h

/-- The marked models form an expander family (tex l.337–342). -/
theorem isExpanderFamily_slMarking {R : Type*} [Ring R] (n : ℕ) (hn : 3 ≤ n)
    [IsSimpleGroup (elementaryGroup (Fin n) R)] [Infinite (elementaryGroup (Fin n) R)]
    (S : Finset R) (hS1 : (1 : R) ∈ S) (hS : Subring.closure (S : Set R) = ⊤)
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) (hφ : IsPrintedMatricial S N φ) :
    SimpleKazhdanSofic.IsExpanderFamily (slMarking n hn S N hN φ) := by
  have h := SimpleKazhdanSofic.IsExpanderFamily.map_target
    (H' := fun k => Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2))
    (isExpanderFamily_matricial n hn S hS1 hS N hN φ hφ)
    (fun k => SimpleKazhdanSofic.elementaryBlockEquivSL n hn (N k) (hN k))
  exact h

/-! ## `thm:general(b)` -/

/-- **Theorem `thm:general`(b)** for a ring `R` with `EL_n(R)` infinite and simple (tex l.178–186,
proof l.316–342): `EL_n(R)` marked by the `e_ij(s)`, `s ∈ S`, is the marked limit of the finite simple
groups `SL_{nN_k}(F₂)` marked by the `e_ij(φ_k(s))`, these form an expander family, and hence `EL_n(R)`
is an expander limit, in the printed vertex-boundary sense (tex l.92–100), of the class of finite
simple groups `SL_{nN}(F₂)`. -/
theorem thm_general_b {R : Type*} [Ring R] (n : ℕ) (hn : 3 ≤ n)
    [IsSimpleGroup (elementaryGroup (Fin n) R)] [Infinite (elementaryGroup (Fin n) R)]
    (S : Finset R) (hS1 : (1 : R) ∈ S) (hS : Subring.closure (S : Set R) = ⊤)
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)) (hφ : IsPrintedMatricial S N φ) :
    SimpleKazhdanSofic.IsMarkedLimit (elementaryMarking n S) (slMarking n hn S N hN φ) ∧
      SimpleKazhdanSofic.IsExpanderFamily (slMarking n hn S N hN φ) ∧
      (∀ k, SK05.IsFiniteSimpleSLMultiple n
        (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2))) ∧
      Tendsto N atTop atTop ∧
      SimpleKazhdanSofic.ThmMainA.IsExpanderLimitOfClass (SK05.IsFiniteSimpleSLMultiple n)
        ↥(elementaryGroup (Fin n) R) := by
  have hlim := isMarkedLimit_slMarking n hn S hS1 hS N hN φ hφ
  have hexp := isExpanderFamily_slMarking n hn S hS1 hS N hN φ hφ
  have hclass : ∀ k, SK05.IsFiniteSimpleSLMultiple n
      (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2)) := fun k =>
    SK05.isFiniteSimpleSLMultiple_blocks n (N k) (isSimpleGroup_sl n hn (N k) (hN k))
  refine ⟨hlim, hexp, hclass, ?_, ?_⟩
  · exact tendsto_N_of_isMarkedLimit n hn S N hN φ hlim
  · obtain ⟨m, g, q, hq⟩ := SimpleKazhdanSofic.ThmMainA.isExpanderLimit_of_isMarkedLimit hlim hexp
    exact ⟨m, g, fun k => Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2),
      fun _ => inferInstance, q, hclass, hq⟩

end GroupApproximation.Full.SK04
