import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormDeepen
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal form: closure under right multiplication by `V_X`

* `rnNF_conj`: suppose `g ∈ V_X` carries every cone of a factor list `P` onto a cone.  Then
  `rfV g * Π P * (rfV g)⁻¹` is again the product of a factor list, obtained by composing each
  `e` with `g`.
* `rnNF_exists_bound`: a finite list has a common bound.
* `rnNF_mul_rfV`: `rfV v * Π P * rfV u` is again in normal form.  First deepen `P` past the
  depth of `u⁻¹`, then conjugate by `u⁻¹`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

/-- A finite list has a common bound. -/
theorem rnNF_exists_bound {α : Type*} (f : α → ℕ) (P : List α) : ∃ M, ∀ p ∈ P, f p ≤ M := by
  induction P with
  | nil => exact ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | cons a P ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨max (f a) M, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | h
    · exact le_max_left _ _
    · exact (hM p h).trans (le_max_right _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_exists_bound

variable [Finite X] [Nontrivial X]

/-- **Conjugating a factor list.** -/
theorem rnNF_conj (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (x₀ : X) (g : ↥(higmanThompsonV X)) :
    ∀ P : List (↥(higmanThompsonV X) × List X × ↥H),
      (∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1) →
      P.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1) →
      (∀ p ∈ P, ∃ c, MapsCone (g : Equiv.Perm (Cantor X)) p.2.1 c) →
      ∃ P'' : List (↥(higmanThompsonV X) × List X × ↥H),
        (∀ a ∈ P'', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
        P''.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
        (∀ b ∈ P'', ∃ p ∈ P, MapsCone (g : Equiv.Perm (Cantor X)) p.2.1 b.2.1) ∧
        rfV H N g * (P.map fun p => rfConjL H N p.1 p.2.2).prod * (rfV H N g)⁻¹ =
          (P''.map fun a => rfConjL H N a.1 a.2.2).prod := by
  intro P
  induction P with
  | nil =>
    intro _ _ _
    exact ⟨[], fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil,
      fun _ h => absurd h List.not_mem_nil,
      by simp only [List.map_nil, List.prod_nil, mul_one, mul_inv_cancel]⟩
  | cons p P ih =>
    intro hv hpair hc
    rw [List.pairwise_cons] at hpair
    obtain ⟨P₀, hv₀, hp₀, hw₀, he₀⟩ :=
      ih (fun q hq => hv q (List.mem_cons_of_mem p hq)) hpair.2
        (fun q hq => hc q (List.mem_cons_of_mem p hq))
    obtain ⟨c, hpc⟩ := hc p List.mem_cons_self
    refine ⟨(g * p.1, c, p.2.2) :: P₀, fun a ha => ?_, ?_, fun b hb => ?_, ?_⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact (hv p List.mem_cons_self).comp hpc
      · exact hv₀ a ha
    · rw [List.pairwise_cons]
      refine ⟨fun b hb => ?_, hp₀⟩
      obtain ⟨q, hq, hqb⟩ := hw₀ b hb
      exact rnNF_incomp_image hpc hqb (hpair.1 q hq)
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨p, List.mem_cons_self, hpc⟩
      · obtain ⟨q, hq, hqb⟩ := hw₀ b hb
        exact ⟨q, List.mem_cons_of_mem p hq, hqb⟩
    · simp only [List.map_cons, List.prod_cons]
      rw [← he₀, ← rcore_conj_rfConjL H N g p.1 p.2.2]
      simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_conj

/-- **Step B.** Right multiplication by `rfV u` keeps the normal form. -/
theorem rnNF_mul_rfV (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hsplit : nfSplitRelators H x₀ ⊆ N) (v : ↥(higmanThompsonV X))
    (P : List (↥(higmanThompsonV X) × List X × ↥H))
    (hv : ∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1)
    (hpair : P.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1))
    (u : ↥(higmanThompsonV X)) :
    ∃ (v' : ↥(higmanThompsonV X)) (P'' : List (↥(higmanThompsonV X) × List X × ↥H)),
      (∀ a ∈ P'', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
      P''.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
      rfV H N v * (P.map fun p => rfConjL H N p.1 p.2.2).prod * rfV H N u =
        rfV H N v' * (P''.map fun a => rfConjL H N a.1 a.2.2).prod := by
  obtain ⟨D, hD⟩ := mem_higmanThompsonV.mp (u⁻¹).2
  obtain ⟨B, hB⟩ := rnNF_exists_bound
    (fun p : ↥(higmanThompsonV X) × List X × ↥H => p.2.1.length) P
  obtain ⟨s, P₁, hv₁, hp₁, hl₁, he₁⟩ := rnNF_deepen H N hH x₀ hcomm hsplit (D + B) P hv hpair
    fun p hp => (hB p hp).trans (Nat.le_add_left B D)
  obtain ⟨P₂, hv₂, hp₂, -, he₂⟩ := rnNF_conj H N x₀ u⁻¹ P₁ hv₁ hp₁
    fun p hp => hD.mono (Nat.le_add_right D B) p.2.1 (hl₁ p hp)
  refine ⟨v * s * u, P₂, hv₂, hp₂, ?_⟩
  rw [he₁, ← he₂, map_inv, map_mul, map_mul]
  simp only [inv_inv, mul_assoc, mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_mul_rfV

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
