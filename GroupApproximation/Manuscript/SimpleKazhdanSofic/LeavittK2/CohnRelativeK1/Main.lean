import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.Spanning
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.Quotient
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.Representation
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative `K_1(C_2, I) = 0` for the local-unit ideal `I = (p)`

Lane `sk-leavitt-19`, seventh module (lane endpoint).

**Truth check.**
* The statement is true over `F_2` in every rank `#ι ≥ 2`.
* It is **false in rank 1**: `1 + e p` is a unit, with inverse `1 - e p`, congruent to
  `1` modulo `I`, and `E_1` is trivial.  Hence the hypothesis `[Nontrivial ι]`.
* It is also false over a general field `k`: there `K_1(C_2, I) ≅ K_1(k) = k^×`.  Over
  `F_2`, `GL_N(F_2) = E_N(F_2)`, which is why the statement is specific to `F_2`.

Route.
1. The monomials `α β*` span `C_2(F_2)` (`cohnTwo_mem_monomialSpan`).  This is induction
   over the free algebra, using `Spanning.lean`.
2. `p ≠ 0` (`cohnTwo_p_ne_zero`): `p` acts on the Fock space as the projection onto the
   empty word (`CohnTwo.fock_p`).
3. So `I = (p)` is the `F_2`-span of the matrix units (`mem_unitSpan_of_mem_span_p`).
   If `u ≡ 1 (mod I)` then also `u⁻¹ ≡ 1` (`inv_sub_one_mem`).
4. Excision (`mem_relativeElementary_of_unitSpan`) puts `u` in a corner `M_N(F_2)`, and
   `GL_N(F_2) = E_N(F_2)` plus the commutator trick gives `u ∈ EL_ι(C_2, I)`.

Lane 18 (`CohnTwo.cohnRelativeKOneTrivial` in `CohnTwo/RelativeKOne.lean`) uses the same
excision lemmas for the rank-`Fin n` form `CohnRelativeKOneTrivialStatement`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

/-- Each generator of `C_2(F_2)` is one of `e, f, e*, f*` of the Cohn data. -/
theorem cohnTwo_generator_cases (g : BinaryLeavitt.Generator) :
    CohnTwo.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) g) = (CohnTwo.data (ZMod 2)).gen 0 ∨
      CohnTwo.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) g) = (CohnTwo.data (ZMod 2)).gen 1 ∨
      CohnTwo.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) g) = (CohnTwo.data (ZMod 2)).gs 0 ∨
      CohnTwo.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) g) = (CohnTwo.data (ZMod 2)).gs 1 := by
  rcases g with ⟨_ | _ | _ | _ | n, hn⟩
  · exact Or.inl (CohnTwo.data (ZMod 2)).gen_zero.symm
  · exact Or.inr (Or.inl (CohnTwo.data (ZMod 2)).gen_one.symm)
  · exact Or.inr (Or.inr (Or.inl (CohnTwo.data (ZMod 2)).gs_zero.symm))
  · exact Or.inr (Or.inr (Or.inr (CohnTwo.data (ZMod 2)).gs_one.symm))
  · exfalso
    omega

/-- The monomials `α β*` span `C_2(F_2)`. -/
theorem cohnTwo_mem_monomialSpan (r : CohnTwo (ZMod 2)) :
    r ∈ (CohnTwo.data (ZMod 2)).monomialSpan := by
  have key : ∀ x : BinaryLeavitt.Free (ZMod 2), ∀ m ∈ (CohnTwo.data (ZMod 2)).monomialSpan,
      CohnTwo.quotientMap (ZMod 2) x * m ∈ (CohnTwo.data (ZMod 2)).monomialSpan := by
    intro x
    induction x using FreeAlgebra.induction with
    | grade0 c =>
      intro m hm
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact (CohnTwo.data (ZMod 2)).monomialSpan.smul_mem c hm
    | grade1 g =>
      intro m hm
      rcases cohnTwo_generator_cases g with h | h | h | h <;> rw [h]
      · exact (CohnTwo.data (ZMod 2)).gen_mul_mem_monomialSpan 0 hm
      · exact (CohnTwo.data (ZMod 2)).gen_mul_mem_monomialSpan 1 hm
      · exact (CohnTwo.data (ZMod 2)).gs_mul_mem_monomialSpan 0 hm
      · exact (CohnTwo.data (ZMod 2)).gs_mul_mem_monomialSpan 1 hm
    | mul a b ha hb =>
      intro m hm
      rw [map_mul, mul_assoc]
      exact ha _ (hb m hm)
    | add a b ha hb =>
      intro m hm
      rw [map_add, add_mul]
      exact (CohnTwo.data (ZMod 2)).monomialSpan.add_mem (ha m hm) (hb m hm)
  obtain ⟨x, rfl⟩ := CohnTwo.quotientMap_surjective (ZMod 2) r
  have h1 := key x 1 (CohnTwo.data (ZMod 2)).one_mem_monomialSpan
  rw [mul_one] at h1
  exact h1

/-- `p ≠ 0` in `C_2(F_2)`: it acts as the projection onto the empty word. -/
theorem cohnTwo_p_ne_zero : (CohnTwo.data (ZMod 2)).p ≠ 0 := by
  intro h
  have h1 := CohnTwo.fock_p (ZMod 2) (CohnTwo.pt (ZMod 2) [] 1)
  rw [h, map_zero, LinearMap.zero_apply] at h1
  have h2 := congr_fun h1 []
  have h3 : CohnTwo.pt (ZMod 2) [] (CohnTwo.pt (ZMod 2) [] (1 : ZMod 2) []) [] = 1 := by
    simp [CohnTwo.pt]
  exact zero_ne_one (show (0 : ZMod 2) = 1 from h2.trans h3)

/-- If `u ≡ 1` entrywise modulo a two-sided ideal, then so is `u⁻¹`. -/
theorem inv_sub_one_mem {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
    (I : TwoSidedIdeal R) (u : (Matrix ι ι R)ˣ)
    (hu : ∀ i j, ((u : Matrix ι ι R) - 1) i j ∈ I) (i j : ι) :
    (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1) i j ∈ I := by
  have h : ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) - 1 =
      -(((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) * ((u : Matrix ι ι R) - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [h, Matrix.neg_apply]
  exact I.neg_mem (entry_mul_mem_of_right I _ hu i j)

/-- **Lane endpoint: relative `K_1(C_2, I) = 0`.**  Take `C_2 = C_2(F_2)`,
`I = (p)` with `p = 1 - ee* - ff*`, and any finite rank `#ι ≥ 2`.  Every invertible
matrix congruent to `1` modulo `I` lies in the relative elementary group `EL_ι(C_2, I)`. -/
theorem cohnTwo_relativeK1_trivial {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (u : (Matrix ι ι (CohnTwo (ZMod 2)))ˣ)
    (hu : ∀ i j, ((u : Matrix ι ι (CohnTwo (ZMod 2))) - 1) i j ∈ CohnTwo.pIdeal (ZMod 2)) :
    ∃ g ∈ relativeElementary ι (CohnTwo.pIdeal (ZMod 2)),
      (g : (Matrix ι ι (CohnTwo (ZMod 2)))ˣ) = u :=
  (CohnTwo.data (ZMod 2)).mem_relativeElementary_of_unitSpan cohnTwo_p_ne_zero
    (CohnTwo.pIdeal (ZMod 2)) (TwoSidedIdeal.subset_span (Set.mem_singleton _)) u
    (fun i j => (CohnTwo.data (ZMod 2)).mem_unitSpan_of_mem_span_p cohnTwo_mem_monomialSpan
      (hu i j))
    (fun i j => (CohnTwo.data (ZMod 2)).mem_unitSpan_of_mem_span_p cohnTwo_mem_monomialSpan
      (inv_sub_one_mem (CohnTwo.pIdeal (ZMod 2)) u hu i j))

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.cohnTwo_generator_cases
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.cohnTwo_mem_monomialSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.cohnTwo_p_ne_zero
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.inv_sub_one_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeK1.cohnTwo_relativeK1_trivial
