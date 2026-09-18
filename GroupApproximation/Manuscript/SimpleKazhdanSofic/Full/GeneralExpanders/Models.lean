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
  have h2 := congrArg Units.val h
  exact h2

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
    (SimpleKazhdanSofic.elementaryBlockEquivSL n hn N hN).injective.nontrivial
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

/-- If the orders of `SL_{n × N_k}(F₂)` tend to infinity, then so do the `N_k`, since
`|SL_{n × N}(F₂)| ≤ 2^{(nN)²}`. -/
theorem tendsto_N_of_tendsto_card (n : ℕ) (N : ℕ → ℕ)
    (h : Tendsto (fun k => Nat.card (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2)))
      atTop atTop) :
    Tendsto N atTop atTop := by
  rw [tendsto_atTop_atTop] at h ⊢
  intro B
  obtain ⟨K, hK⟩ := h (2 ^ ((n * B) * (n * B)) + 1)
  refine ⟨K, fun k hk => ?_⟩
  by_contra hlt
  have hNk : N k ≤ B := by omega
  have h1 := Nat.card_le_card_of_injective
    (fun A : Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2) =>
      fun (i j : Fin n × Fin (N k)) =>
        (A : Matrix (Fin n × Fin (N k)) (Fin n × Fin (N k)) (ZMod 2)) i j)
    (fun A A' hAA' => Subtype.ext hAA')
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2)) ≤
      2 ^ ((n * N k) * (n * N k)) := by
    calc Nat.card (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2))
        ≤ Nat.card (Fin n × Fin (N k) → Fin n × Fin (N k) → ZMod 2) := h1
      _ = 2 ^ ((n * N k) * (n * N k)) := by
        rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, ← Nat.pow_mul]
  have hpow : 2 ^ ((n * N k) * (n * N k)) ≤ 2 ^ ((n * B) * (n * B)) :=
    Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul (Nat.mul_le_mul (le_refl n) hNk) (Nat.mul_le_mul (le_refl n) hNk))
  exact Nat.lt_irrefl _ (lt_of_lt_of_le (Nat.lt_succ_of_le (hcard.trans hpow)) (hK k hk))

/-! ## The hypothesis `0 < N k` is necessary -/

/-- The zero maps `φ_k = 0 : R → M_0(F₂)` satisfy every printed condition on the `φ_k`
(`simple_kazhdan_sofic_group.tex`, `thm:general`(b), tex l.180–184). -/
theorem isPrintedMatricial_zero {R : Type*} [Ring R] (S : Finset R) :
    IsPrintedMatricial S (fun _ => 0) (fun _ _ => 0) := by
  have hsub : ∀ A B : Matrix (Fin 0) (Fin 0) (ZMod 2), A = B := fun _ _ =>
    Matrix.ext fun i _ => Fin.elim0 i
  refine ⟨fun _ => hsub _ _, fun _ => eq_top_iff.mpr fun x _ => ?_, fun _ _ =>
    Filter.Eventually.of_forall fun _ => ⟨hsub _ _, hsub _ _⟩⟩
  rw [hsub x 0]
  exact Subring.zero_mem _

/-- `SL_{n × 0}(F₂)` is trivial, hence not simple. -/
theorem not_isSimpleGroup_sl_zero (n : ℕ) :
    ¬ IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n × Fin 0) (ZMod 2)) := by
  intro hsimple
  haveI := hsimple
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Matrix.SpecialLinearGroup (Fin n × Fin 0) (ZMod 2))
  exact hxy (Matrix.SpecialLinearGroup.ext x y fun i _ => Fin.elim0 i.2)

/-- **The correction `0 < N k` is necessary** (tex l.180–186): without it the printed conditions on the
`φ_k` are satisfied by `N_k = 0` and the zero maps, and then none of the groups `SL_{nN_k}(F₂)` is
simple, so the printed conclusion ("the finite simple groups `SL_{nN_k}(F₂)`") fails. -/
theorem exists_printedMatricial_not_simple (n : ℕ) {R : Type*} [Ring R] (S : Finset R) :
    ∃ (N : ℕ → ℕ) (φ : ∀ k, R → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
      IsPrintedMatricial S N φ ∧
        ∀ k, ¬ IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2)) :=
  ⟨fun _ => 0, fun _ _ => 0, isPrintedMatricial_zero S, fun _ => not_isSimpleGroup_sl_zero n⟩

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
  · exact tendsto_N_of_tendsto_card n N (tendsto_card_of_isMarkedLimit hlim (fun _ => inferInstance))
  · obtain ⟨m, g, q, hq⟩ := SimpleKazhdanSofic.ThmMainA.isExpanderLimit_of_isMarkedLimit hlim hexp
    exact ⟨m, g, fun k => Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2),
      fun _ => inferInstance, q, hclass, hq⟩

/-- **Theorem `thm:general`(b)** in the printed setting (tex l.172–186): let a finitely generated group
`Λ` act minimally and topologically freely on a Cantor set `C`, let `R = LC(C, F₂) ⋊ Λ` be generated by
a finite set `S ∋ 1`, and let `φ_k : R → M_{N_k}(F₂)` (`N_k ≥ 1`) satisfy `φ_k(1) = I`, `φ_k(S)`
generates `M_{N_k}(F₂)`, and `φ_k` is eventually additive and multiplicative on each pair. Then for
`n ≥ 3`, `EL_n(R)` marked by the `e_ij(s)` is the marked limit of the finite simple groups
`SL_{nN_k}(F₂)` marked by the `e_ij(φ_k(s))`, these form an expander family, `N_k → ∞`, and `EL_n(R)`
is an expander limit (tex l.92–100) of finite simple groups `SL_{nN}(F₂)`. Infinitude and simplicity
of `EL_n(R)` come from part (a), `Full.SK03.printedGeneralPartA`. -/
theorem thm_general_b_printed (Λ : Type) [Group Λ] [Group.FG Λ] (C : Type) [TopologicalSpace C]
    [CompactSpace C] [TopologicalSpace.MetrizableSpace C] [TotallyDisconnectedSpace C]
    [PerfectSpace C] [Nonempty C] [MulAction Λ C] [ContinuousConstSMul Λ C]
    (hmin : MulAction.IsMinimal Λ C)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set C, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ C (ZMod 2)))
    (hS1 : (1 : ClopenGroupCrossedProduct Λ C (ZMod 2)) ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ C (ZMod 2))) = ⊤)
    (n : ℕ) (hn : 3 ≤ n) (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ C (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsPrintedMatricial S N φ) :
    SimpleKazhdanSofic.IsMarkedLimit (elementaryMarking n S) (slMarking n hn S N hN φ) ∧
      SimpleKazhdanSofic.IsExpanderFamily (slMarking n hn S N hN φ) ∧
      (∀ k, SK05.IsFiniteSimpleSLMultiple n
        (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2))) ∧
      Tendsto N atTop atTop ∧
      SimpleKazhdanSofic.ThmMainA.IsExpanderLimitOfClass (SK05.IsFiniteSimpleSLMultiple n)
        ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) := by
  obtain ⟨hinf, -, hsimple, -⟩ := SK03.printedGeneralPartA Λ C hmin hfree S hS1 hS n hn
  haveI := hinf
  haveI := hsimple
  exact thm_general_b n hn S hS1 hS N hN φ hφ

#audit_axioms coe_elementaryBlockEquivSL_apply
#audit_axioms isSimpleGroup_sl
#audit_axioms tendsto_N_of_tendsto_card
#audit_axioms exists_printedMatricial_not_simple
#audit_axioms thm_general_b
#audit_axioms thm_general_b_printed

end GroupApproximation.Full.SK04
