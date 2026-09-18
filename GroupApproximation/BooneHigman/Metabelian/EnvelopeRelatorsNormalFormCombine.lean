import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal form: rewriting each factor of a product

Work in `Q = RNFree X H ⧸ N`, where `N` contains the commutation relators.  A *factor list* is
a list `P` of triples `(e, w, k)` with `e : cone [x₀] → cone w` and pairwise incomparable
words `w`.  Its product is `Π rfConjL e k`.

`rnNF_combine`: suppose every factor `rfConjL e k` of `P` is rewritten as `rfV s * Π P_p`, where
`s` fixes every stream outside `cone w` and the words of `P_p` extend `w`.  Then the whole
product is `rfV s * Π P'`, where `P'` is the concatenation of the lists `P_p`.  The shifts move
to the left because each one fixes the cones of the later factors.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

theorem rnNF_mul_swap {G : Type*} [Group G] {a b c d : G} (h : Commute b c) :
    a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_assoc]
  rw [← mul_assoc b c d, h.eq, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_mul_swap

variable [Finite X]

/-- **Combining rewritten factors.** -/
theorem rnNF_combine (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N) (R : List X → Prop) :
    ∀ P : List (↥(higmanThompsonV X) × List X × ↥H),
      (∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1) →
      P.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1) →
      (∀ p ∈ P, ∃ (s : ↥(higmanThompsonV X)) (P' : List (↥(higmanThompsonV X) × List X × ↥H)),
        (∀ z, ¬ IsStreamPrefix p.2.1 z → (s : Equiv.Perm (Cantor X)) z = z) ∧
        (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
        P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
        (∀ a ∈ P', p.2.1 <+: a.2.1 ∧ R a.2.1) ∧
        rfConjL H N p.1 p.2.2 = rfV H N s * (P'.map fun a => rfConjL H N a.1 a.2.2).prod) →
      ∃ (s : ↥(higmanThompsonV X)) (P' : List (↥(higmanThompsonV X) × List X × ↥H)),
        (∀ z, (∀ p ∈ P, ¬ IsStreamPrefix p.2.1 z) → (s : Equiv.Perm (Cantor X)) z = z) ∧
        (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
        P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
        (∀ a ∈ P', (∃ p ∈ P, p.2.1 <+: a.2.1) ∧ R a.2.1) ∧
        (P.map fun p => rfConjL H N p.1 p.2.2).prod =
          rfV H N s * (P'.map fun a => rfConjL H N a.1 a.2.2).prod := by
  intro P
  induction P with
  | nil =>
    intro _ _ _
    exact ⟨1, [], fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil,
      fun _ h => absurd h List.not_mem_nil,
      by simp only [List.map_nil, List.prod_nil, map_one, mul_one]⟩
  | cons p P ih =>
    intro hv hpair hsplit
    rw [List.pairwise_cons] at hpair
    obtain ⟨s₀, P₀, hs₀, hv₀, hp₀, hw₀, he₀⟩ :=
      ih (fun q hq => hv q (List.mem_cons_of_mem p hq)) hpair.2
        (fun q hq => hsplit q (List.mem_cons_of_mem p hq))
    obtain ⟨s₁, P₁, hs₁, hv₁, hp₁, hw₁, he₁⟩ := hsplit p List.mem_cons_self
    have hfix : ∀ a ∈ P₁, MapsCone (s₀ : Equiv.Perm (Cantor X)) a.2.1 a.2.1 := fun a ha y =>
      hs₀ _ fun q hq => rnNF_not_isStreamPrefix (hw₁ a ha).1
        ⟨(hpair.1 q hq).2, (hpair.1 q hq).1⟩ y
    have hc := rnNF_commute_rfV_prod H N x₀ hcomm s₀ P₁ hv₁ hfix
    refine ⟨s₁ * s₀, P₁ ++ P₀, fun z hz => ?_, fun a ha => ?_, ?_, fun a ha => ?_, ?_⟩
    · rw [Subgroup.coe_mul, Equiv.Perm.mul_apply,
        hs₀ z (fun q hq => hz q (List.mem_cons_of_mem p hq)), hs₁ z (hz p List.mem_cons_self)]
    · rcases List.mem_append.mp ha with ha | ha
      · exact hv₁ a ha
      · exact hv₀ a ha
    · rw [List.pairwise_append]
      refine ⟨hp₁, hp₀, fun a ha b hb => ?_⟩
      obtain ⟨⟨q, hq, hqb⟩, -⟩ := hw₀ b hb
      exact rnNF_incomp_mono (hw₁ a ha).1 hqb (hpair.1 q hq)
    · rcases List.mem_append.mp ha with ha | ha
      · exact ⟨⟨p, List.mem_cons_self, (hw₁ a ha).1⟩, (hw₁ a ha).2⟩
      · obtain ⟨⟨q, hq, hqa⟩, hR⟩ := hw₀ a ha
        exact ⟨⟨q, List.mem_cons_of_mem p hq, hqa⟩, hR⟩
    · simp only [List.map_cons, List.prod_cons]
      rw [he₁, he₀, List.map_append, List.prod_append, map_mul (rfV H N) s₁ s₀]
      exact rnNF_mul_swap hc.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_combine

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
