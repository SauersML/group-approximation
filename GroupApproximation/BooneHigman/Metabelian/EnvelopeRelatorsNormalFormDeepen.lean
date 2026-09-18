import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal form: deepening a factor list, and splitting with the shift on the right

* `rnNF_deepen`: a factor list whose words have length `≤ M` equals `rfV s * Π P'` for some
  factor list `P'` whose words all have length exactly `M`.
* `rnNF_prod_inv`: the inverse of a list product.
* `rnNF_split_right`: `rfConjL e k = Π P' * rfV s`, where the words of `P'` extend `w` by
  exactly `n` letters.  This is `rnNF_split_deep` applied to `k⁻¹` and then inverted.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*}

/-- The inverse of a list product. -/
theorem rnNF_prod_inv {G ι : Type*} [Group G] (f : ι → G) (L : List ι) :
    (L.map f).prod⁻¹ = (L.reverse.map fun a => (f a)⁻¹).prod := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, inv_one, List.reverse_nil]
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, mul_inv_rev, ih, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_prod_inv

variable [Finite X] [Nontrivial X]

/-- **Deepening.** Every word of the factor list is pushed down to length exactly `M`. -/
theorem rnNF_deepen (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hsplit : nfSplitRelators H x₀ ⊆ N) (M : ℕ)
    (P : List (↥(higmanThompsonV X) × List X × ↥H))
    (hv : ∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1)
    (hpair : P.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1))
    (hM : ∀ p ∈ P, p.2.1.length ≤ M) :
    ∃ (s : ↥(higmanThompsonV X)) (P' : List (↥(higmanThompsonV X) × List X × ↥H)),
      (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
      P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
      (∀ a ∈ P', a.2.1.length = M) ∧
      (P.map fun p => rfConjL H N p.1 p.2.2).prod =
        rfV H N s * (P'.map fun a => rfConjL H N a.1 a.2.2).prod := by
  obtain ⟨s, P', -, hv', hp', hw', heq⟩ :=
    rnNF_combine H N x₀ hcomm (fun u => u.length = M) P hv hpair fun p hp => by
      obtain ⟨s, P', hs, hva, hpa, hwa, hea⟩ :=
        rnNF_split_deep H N hH x₀ hcomm hsplit (M - p.2.1.length) p.1 p.2.1 p.2.2 (hv p hp)
      refine ⟨s, P', hs, hva, hpa, fun a ha => ⟨(hwa a ha).1, ?_⟩, hea⟩
      have h1 := (hwa a ha).2
      have h2 := hM p hp
      show a.2.1.length = M
      omega
  exact ⟨s, P', hv', hp', fun a ha => (hw' a ha).2, heq⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_deepen

/-- **Splitting with the shift on the right.** -/
theorem rnNF_split_right (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hsplit : nfSplitRelators H x₀ ⊆ N) (n : ℕ) (e : ↥(higmanThompsonV X)) (w : List X)
    (k : ↥H) (he : MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w) :
    ∃ (s : ↥(higmanThompsonV X)) (P' : List (↥(higmanThompsonV X) × List X × ↥H)),
      (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
      P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
      (∀ a ∈ P', w <+: a.2.1 ∧ a.2.1.length = w.length + n) ∧
      rfConjL H N e k = (P'.map fun a => rfConjL H N a.1 a.2.2).prod * rfV H N s := by
  obtain ⟨s, S, -, hv, hp, hw, heq⟩ := rnNF_split_deep H N hH x₀ hcomm hsplit n e w k⁻¹ he
  refine ⟨s⁻¹, S.reverse.map fun a => (a.1, a.2.1, a.2.2⁻¹), fun a ha => ?_, ?_,
    fun a ha => ?_, ?_⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hv b (List.mem_reverse.mp hb)
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact hp.imp fun h => ⟨h.2, h.1⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hw b (List.mem_reverse.mp hb)
  · have h1 : rfConjL H N e k = (rfConjL H N e k⁻¹)⁻¹ := by rw [map_inv, inv_inv]
    rw [h1, heq, mul_inv_rev, rnNF_prod_inv, map_inv, List.map_map]
    congr 1
    refine congrArg List.prod (List.map_congr_left fun a _ => ?_)
    exact (map_inv (rfConjL H N a.1) a.2.2).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_split_right

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
