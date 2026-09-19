import GroupApproximation.BooneHigman.Join.DPresent

/-!
# The all-swaps relators present `V_d` (lane bh-pal-met-join)

**`higmanVC_ker_le_all`**: for every `d > 1`,
`ker (higmanVC_evalAll d) ≤ normalClosure (higmanVC_rels d ⊤)`.  No hypotheses.

* `jH_eq_one_of_monoD`: an element of an antichain subgroup whose action is monotone is `1`.
  Its permutation of the antichain preserves the order `DBefore` of the cones, so it is
  trivial (rank counting), and antichain faithfulness gives triviality in `Q`.
* `N_kerD`: `f · σ` with trivial action, `f ∈ PhiD`, `σ ∈ jH C`, is `1`.
* `eq_one_of_jpermD`: the evaluation of `Q` is injective (every element is a normal form).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- An order-preserving permutation of a finite strict total order is the identity. -/
theorem perm_eq_one_of_monoD {α : Type*} [Fintype α] (r : α → α → Prop)
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

#audit_axioms GroupApproximation.BooneHigman.Join.perm_eq_one_of_monoD

/-- An element of an antichain subgroup acting monotonically is trivial. -/
theorem jH_eq_one_of_monoD {C : Finset (List (Fin (n + 2)))} (hC : IsAC C)
    {σ : higmanVCCommon_Q (n + 2)} (hσ : σ ∈ jH (n + 2) C) (hm : DMono (jperm (n + 2) σ)) :
    σ = 1 := by
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hσ
  have hmc := higmanVCAll_mapsCone_word hC r
  have hπ : FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r = 1 := by
    refine perm_eq_one_of_monoD (fun a b : ↥C => DBefore a.1 b.1) (fun a => dbefore_irrefl a.1)
      (fun a b c => dbefore_trans) (fun a b hab => ?_) _ (fun a b h y z => ?_)
    · have hne : a.1 ≠ b.1 := fun e => hab (Subtype.ext e)
      exact dbefore_or_dbefore (hC a.1 a.2 b.1 b.2 hne) (hC b.1 b.2 a.1 a.2 (Ne.symm hne))
    · have h' : DLt (jperm (n + 2) (((higmanVCCommon_mk (n + 2)).comp (higmanVCAll_iota C)) r)
          (prepend a.1 y))
          (jperm (n + 2) (((higmanVCCommon_mk (n + 2)).comp (higmanVCAll_iota C)) r)
          (prepend b.1 z)) := hm _ _ (h y z)
      have ha : jperm (n + 2) (((higmanVCCommon_mk (n + 2)).comp (higmanVCAll_iota C)) r)
          (prepend a.1 y) = prepend (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r a).1 y :=
        hmc a y
      have hb : jperm (n + 2) (((higmanVCCommon_mk (n + 2)).comp (higmanVCAll_iota C)) r)
          (prepend b.1 z) = prepend (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r b).1 z :=
        hmc b z
      rw [ha, hb] at h'
      exact h'
  have h1 : higmanVCAll_iota C r ∈ Subgroup.normalClosure (higmanVC_rels (n + 2) fun _ => True) := by
    rw [← QuotientGroup.ker_mk' (Subgroup.normalClosure (higmanVC_rels (n + 2) fun _ => True)),
      MonoidHom.mem_ker, higmanVCAll_mk_iota]
    exact higmanVCAll_lift_eq_one (higmanVCAll_gen (n + 2) C) higmanVCAll_gen_self
      higmanVCAll_gen_sq (higmanVCAll_gen_conj hC) r hπ
  exact higmanVCCommon_mk_eq_one_iff.mpr h1

#audit_axioms GroupApproximation.BooneHigman.Join.jH_eq_one_of_monoD

/-- **The normal forms meet the kernel trivially.** -/
theorem N_kerD {C : Finset (List (Fin (n + 2)))} (hC : IsAC C) {f σ : higmanVCCommon_Q (n + 2)}
    (hf : f ∈ PhiD n) (hσ : σ ∈ jH (n + 2) C) (h : jperm (n + 2) (f * σ) = 1) : f * σ = 1 := by
  have hs : jperm (n + 2) σ = (jperm (n + 2) f)⁻¹ := by
    rw [jperm_mul] at h
    exact eq_inv_of_mul_eq_one_right h
  have hm : DMono (jperm (n + 2) σ) := by
    rw [hs]
    exact (dmono_of_mem hf).inv
  have hσ1 := jH_eq_one_of_monoD hC hσ hm
  rw [hσ1, mul_one] at h ⊢
  exact PhiD_faithful hf h

#audit_axioms GroupApproximation.BooneHigman.Join.N_kerD

/-- **The evaluation of the all-swaps quotient of `V_{n+2}` is injective.** -/
theorem eq_one_of_jpermD {q : higmanVCCommon_Q (n + 2)} (h : jperm (n + 2) q = 1) : q = 1 := by
  obtain ⟨f, hf, L, hL, σ, hσ, rfl⟩ := mem_JND q
  exact N_kerD hL.isAC hf hσ h

#audit_axioms GroupApproximation.BooneHigman.Join.eq_one_of_jpermD

/-- **The all-swaps relators present `V_{n+2}`.** -/
theorem higmanVC_ker_le_D (n : ℕ) :
    (higmanVC_evalAll (n + 2)).ker ≤
      Subgroup.normalClosure (higmanVC_rels (n + 2) fun _ => True) := by
  intro r hr
  refine higmanVCCommon_mk_eq_one_iff.mp (eq_one_of_jpermD ?_)
  show ((higmanVC_evalAll (n + 2) r : ↥(higmanThompsonV (Fin (n + 2)))) :
    Equiv.Perm (Cantor (Fin (n + 2)))) = 1
  exact (congrArg Subtype.val (MonoidHom.mem_ker.mp hr)).trans (Subgroup.coe_one _)

#audit_axioms GroupApproximation.BooneHigman.Join.higmanVC_ker_le_D

/-- **The all-swaps relators present `V_d`, for every `d > 1`.** -/
theorem higmanVC_ker_le_all : ∀ d : ℕ, 1 < d →
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
  intro d hd
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  exact higmanVC_ker_le_D n

#audit_axioms GroupApproximation.BooneHigman.Join.higmanVC_ker_le_all

end GroupApproximation.BooneHigman.Join
