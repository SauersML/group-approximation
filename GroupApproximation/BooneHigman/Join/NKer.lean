import GroupApproximation.BooneHigman.Join.Order

/-!
# The normal forms `Phi · jH C` meet the kernel trivially (lane bh-pal-met-join)

* `perm_eq_one_of_mono`: a permutation of a finite set preserving a strict total order is the
  identity (rank counting).
* `jH_eq_one_of_mono`: an element of an antichain subgroup whose boundary action is monotone is
  `1`.  Its permutation of the antichain preserves the order `Before` of the cones, hence is
  trivial, and `higmanVCAll_lift_eq_one` gives triviality in `Q`.
* `N_ker`: if `f ∈ Phi`, `σ ∈ jH 2 C` and `f · σ` acts trivially on the boundary, then
  `f · σ = 1`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

/-- An order-preserving permutation of a finite strict total order is the identity. -/
theorem perm_eq_one_of_mono {α : Type*} [Fintype α] (r : α → α → Prop)
    (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    (htot : ∀ a b, a ≠ b → r a b ∨ r b a) (π : Equiv.Perm α)
    (hπ : ∀ a b, r a b → r (π a) (π b)) : π = 1 := by
  classical
  have hinv : ∀ a b, r (π a) (π b) → r a b := by
    intro a b h
    by_contra hc
    have hne : a ≠ b := fun e => hirr (π a) (by rw [e] at h ⊢; exact h)
    rcases htot a b hne with h' | h'
    · exact hc h'
    · exact hirr _ (htr _ _ _ h (hπ _ _ h'))
  let rk : α → ℕ := fun a => (Finset.univ.filter (fun b => r b a)).card
  have rk_lt : ∀ a b, r a b → rk a < rk b := by
    intro a b h
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact htr _ _ _ hc h
    · intro he
      have ha : a ∈ Finset.univ.filter (fun c => r c b) := by simp [h]
      rw [← he] at ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact hirr a ha
  have rk_eq : ∀ a, rk (π a) = rk a := by
    intro a
    have e : Finset.univ.filter (fun b => r b (π a)) =
        (Finset.univ.filter (fun b => r b a)).image π := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hb
        refine ⟨π⁻¹ b, hinv _ _ ?_, by simp⟩
        simpa using hb
      · rintro ⟨c, hc, rfl⟩
        exact hπ _ _ hc
    show (Finset.univ.filter (fun b => r b (π a))).card = _
    rw [e, Finset.card_image_of_injective _ π.injective]
  ext a
  by_contra hne
  rcases htot a (π a) (Ne.symm hne) with h | h
  · exact absurd (rk_eq a) (Nat.ne_of_gt (rk_lt _ _ h))
  · exact absurd (rk_eq a) (Nat.ne_of_lt (rk_lt _ _ h))

#audit_axioms GroupApproximation.BooneHigman.Join.perm_eq_one_of_mono

/-- An element of an antichain subgroup acting monotonically is trivial. -/
theorem jH_eq_one_of_mono {C : Finset (List (Fin 2))} (hC : IsAC C)
    {σ : higmanVCCommon_Q 2} (hσ : σ ∈ jH 2 C) (hm : IsMono (jperm 2 σ)) : σ = 1 := by
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hσ
  have hmc := higmanVCAll_mapsCone_word hC r
  have hπ : FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r = 1 := by
    refine perm_eq_one_of_mono (fun a b : ↥C => Before a.1 b.1) (fun a => before_irrefl a.1)
      (fun a b c => before_trans) (fun a b hab => ?_) _ (fun a b h y z => ?_)
    · have hne : a.1 ≠ b.1 := fun e => hab (Subtype.ext e)
      exact before_or_before (hC a.1 a.2 b.1 b.2 hne) (hC b.1 b.2 a.1 a.2 (Ne.symm hne))
    · have h' : CLt (((higmanVC_evalAll 2 (higmanVCAll_iota C r) : ↥(higmanThompsonV (Fin 2))) :
            Equiv.Perm (Cantor (Fin 2))) (prepend a.1 y))
          (((higmanVC_evalAll 2 (higmanVCAll_iota C r) : ↥(higmanThompsonV (Fin 2))) :
            Equiv.Perm (Cantor (Fin 2))) (prepend b.1 z)) := hm _ _ (h y z)
      rw [hmc a y, hmc b z] at h'
      exact h'
  have h1 : higmanVCAll_iota C r ∈ Subgroup.normalClosure (higmanVC_rels 2 fun _ => True) := by
    rw [← QuotientGroup.ker_mk' (Subgroup.normalClosure (higmanVC_rels 2 fun _ => True)),
      MonoidHom.mem_ker, higmanVCAll_mk_iota]
    exact higmanVCAll_lift_eq_one (higmanVCAll_gen 2 C) higmanVCAll_gen_self higmanVCAll_gen_sq
      (higmanVCAll_gen_conj hC) r hπ
  exact higmanVCCommon_mk_eq_one_iff.mpr h1

#audit_axioms GroupApproximation.BooneHigman.Join.jH_eq_one_of_mono

/-- **The normal forms meet the kernel trivially.** -/
theorem N_ker {C : Finset (List (Fin 2))} (hC : IsAC C) {f σ : higmanVCCommon_Q 2}
    (hf : f ∈ Phi) (hσ : σ ∈ jH 2 C) (h : jperm 2 (f * σ) = 1) : f * σ = 1 := by
  have hs : jperm 2 σ = (jperm 2 f)⁻¹ := by
    rw [jperm_mul] at h
    exact eq_inv_of_mul_eq_one_right h
  have hm : IsMono (jperm 2 σ) := by
    rw [hs]
    exact (isMono_of_mem_Phi hf).inv
  have hσ1 := jH_eq_one_of_mono hC hσ hm
  rw [hσ1, mul_one] at h ⊢
  exact Phi_faithful hf h

#audit_axioms GroupApproximation.BooneHigman.Join.N_ker

end GroupApproximation.BooneHigman.Join
