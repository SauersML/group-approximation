import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.StableK2
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.Representation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Ideal
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative `K₁(C_2, (p)) = 0` in the concrete Cohn algebra

Lane `sk-leavitt-18`, sixth module.  Lane `sk-leavitt-19` proves excision
(`CohnTwoData.mem_relativeElementary_of_unitSpan`) for any `𝔽₂`-algebra with Cohn data,
under two hypotheses, which are discharged here for `C_2(𝔽₂)`:

* `p ≠ 0` (`data_p_ne_zero`): `p` acts on the Fock space as the projection onto the
  empty word (`fock_p`), and this projection is nonzero.
* the monomials `α β*` span `C_2` (`mem_monomialSpan`): their span contains `1`
  and is stable under left multiplication by the four generators. For `e, f` this
  prepends a letter. For `e*, f*` it either cancels a letter or appends to `β`.
  Then induct over the free algebra.

So `CohnRelativeKOneTrivialStatement` holds (`cohnRelativeKOneTrivial`). The endpoint
`binaryLeavittStableK2Trivial_of_cohnStableK2` leaves stable `K₂(C_2(𝔽₂)) = 0` as the only
input.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

namespace CohnTwo

/-- `p ≠ 0` in `C_2`. -/
theorem data_p_ne_zero (k : Type*) [Field k] : (data k).p ≠ 0 := by
  intro h
  have h1 := fock_p k (pt k [] 1)
  rw [h, map_zero, LinearMap.zero_apply] at h1
  have h2 := congr_fun h1 []
  have h3 : pt k [] (pt k [] (1 : k) []) [] = 1 := by simp [pt]
  exact zero_ne_one (show (0 : k) = 1 from h2.trans h3)

theorem monomial_mem (α β : List (Fin 2)) :
    (data (ZMod 2)).word α * (data (ZMod 2)).coword β ∈ (data (ZMod 2)).monomialSpan := by
  rw [CohnRelativeK1.CohnTwoData.monomialSpan]
  exact Submodule.subset_span ⟨(α, β), rfl⟩

theorem gen_mul_mem (a : Fin 2) {m : CohnTwo (ZMod 2)}
    (hm : m ∈ (data (ZMod 2)).monomialSpan) :
    (data (ZMod 2)).gen a * m ∈ (data (ZMod 2)).monomialSpan := by
  rw [CohnRelativeK1.CohnTwoData.monomialSpan] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨α, β⟩, rfl⟩ := hx
    show (data (ZMod 2)).gen a * ((data (ZMod 2)).word α * (data (ZMod 2)).coword β) ∈ _
    rw [← mul_assoc, ← (data (ZMod 2)).word_cons a α]
    exact monomial_mem (a :: α) β
  | zero =>
    rw [mul_zero]
    exact (data (ZMod 2)).monomialSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact (data (ZMod 2)).monomialSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact (data (ZMod 2)).monomialSpan.smul_mem c hx

theorem gs_mul_mem (a : Fin 2) {m : CohnTwo (ZMod 2)}
    (hm : m ∈ (data (ZMod 2)).monomialSpan) :
    (data (ZMod 2)).gs a * m ∈ (data (ZMod 2)).monomialSpan := by
  rw [CohnRelativeK1.CohnTwoData.monomialSpan] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨α, β⟩, rfl⟩ := hx
    show (data (ZMod 2)).gs a * ((data (ZMod 2)).word α * (data (ZMod 2)).coword β) ∈ _
    cases α with
    | nil =>
      have h : (data (ZMod 2)).gs a * ((data (ZMod 2)).word [] * (data (ZMod 2)).coword β) =
          (data (ZMod 2)).word [] * (data (ZMod 2)).coword (β ++ [a]) := by
        simp only [CohnRelativeK1.CohnTwoData.coword_append,
          CohnRelativeK1.CohnTwoData.coword_cons, CohnRelativeK1.CohnTwoData.coword_nil,
          CohnRelativeK1.CohnTwoData.word_nil, one_mul]
      rw [h]
      exact monomial_mem [] (β ++ [a])
    | cons d α =>
      rw [(data (ZMod 2)).word_cons d α, ← mul_assoc, ← mul_assoc, (data (ZMod 2)).gs_mul_gen]
      by_cases had : a = d
      · rw [if_pos had, one_mul]
        exact monomial_mem α β
      · rw [if_neg had, zero_mul, zero_mul]
        exact (data (ZMod 2)).monomialSpan.zero_mem
  | zero =>
    rw [mul_zero]
    exact (data (ZMod 2)).monomialSpan.zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact (data (ZMod 2)).monomialSpan.add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact (data (ZMod 2)).monomialSpan.smul_mem c hx

theorem generator_mul_mem (g : BinaryLeavitt.Generator) {m : CohnTwo (ZMod 2)}
    (hm : m ∈ (data (ZMod 2)).monomialSpan) :
    generator (ZMod 2) g * m ∈ (data (ZMod 2)).monomialSpan := by
  rcases g with ⟨_ | _ | _ | _ | n, hn⟩
  · have h : generator (ZMod 2) ⟨0, hn⟩ = (data (ZMod 2)).gen 0 :=
      ((data (ZMod 2)).gen_zero).symm
    show generator (ZMod 2) ⟨0, hn⟩ * m ∈ _
    rw [h]
    exact gen_mul_mem 0 hm
  · have h : generator (ZMod 2) ⟨1, hn⟩ = (data (ZMod 2)).gen 1 :=
      ((data (ZMod 2)).gen_one).symm
    show generator (ZMod 2) ⟨1, hn⟩ * m ∈ _
    rw [h]
    exact gen_mul_mem 1 hm
  · have h : generator (ZMod 2) ⟨2, hn⟩ = (data (ZMod 2)).gs 0 :=
      ((data (ZMod 2)).gs_zero).symm
    show generator (ZMod 2) ⟨2, hn⟩ * m ∈ _
    rw [h]
    exact gs_mul_mem 0 hm
  · have h : generator (ZMod 2) ⟨3, hn⟩ = (data (ZMod 2)).gs 1 :=
      ((data (ZMod 2)).gs_one).symm
    show generator (ZMod 2) ⟨3, hn⟩ * m ∈ _
    rw [h]
    exact gs_mul_mem 1 hm
  · exfalso
    omega

/-- The monomials `α β*` span `C_2(𝔽₂)`. -/
theorem mem_monomialSpan (r : CohnTwo (ZMod 2)) : r ∈ (data (ZMod 2)).monomialSpan := by
  have key : ∀ x : BinaryLeavitt.Free (ZMod 2), ∀ m ∈ (data (ZMod 2)).monomialSpan,
      quotientMap (ZMod 2) x * m ∈ (data (ZMod 2)).monomialSpan := by
    intro x
    induction x using FreeAlgebra.induction with
    | grade0 c =>
      intro m hm
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact (data (ZMod 2)).monomialSpan.smul_mem c hm
    | grade1 g =>
      intro m hm
      exact generator_mul_mem g hm
    | mul a b ha hb =>
      intro m hm
      rw [map_mul, mul_assoc]
      exact ha _ (hb m hm)
    | add a b ha hb =>
      intro m hm
      rw [map_add, add_mul]
      exact (data (ZMod 2)).monomialSpan.add_mem (ha m hm) (hb m hm)
  obtain ⟨x, rfl⟩ := quotientMap_surjective (ZMod 2) r
  have h1 := key x _ (monomial_mem [] [])
  simpa only [CohnRelativeK1.CohnTwoData.word_nil, CohnRelativeK1.CohnTwoData.coword_nil,
    mul_one] using h1

/-- Relative `K₁(C_2(𝔽₂), (p)) = 0` at every rank `n ≥ 2`, from lane 19's excision. -/
theorem cohnRelativeKOneTrivial : CohnRelativeKOneTrivialStatement := by
  intro n hn u hu hu'
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact (data (ZMod 2)).mem_relativeElementary_of_unitSpan (data_p_ne_zero (ZMod 2))
    (pIdeal (ZMod 2)) (TwoSidedIdeal.subset_span (Set.mem_singleton _)) u
    (fun i j => (data (ZMod 2)).mem_unitSpan_of_mem_span_p mem_monomialSpan (hu i j))
    (fun i j => (data (ZMod 2)).mem_unitSpan_of_mem_span_p mem_monomialSpan (hu' i j))

end CohnTwo

/-- **Lane endpoint, sharpened.** Stable `K₂(C_2(𝔽₂)) = 0` alone gives stable
`K₂(L_{𝔽₂}(1,2)) = 0`, because relative `K₁` is proved (`cohnRelativeKOneTrivial`). -/
theorem binaryLeavittStableK2Trivial_of_cohnStableK2 (hS : BinaryCohnStableK2TrivialStatement) :
    BinaryLeavittStableK2TrivialStatement :=
  binaryLeavittStableK2Trivial_of_cohn hS CohnTwo.cohnRelativeKOneTrivial

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.data_p_ne_zero
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.monomial_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.gen_mul_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.gs_mul_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.generator_mul_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.mem_monomialSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.cohnRelativeKOneTrivial
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittStableK2Trivial_of_cohnStableK2
