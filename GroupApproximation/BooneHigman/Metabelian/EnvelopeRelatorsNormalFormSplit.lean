import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormCombine
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal form: splitting factors to a prescribed depth

Work in `Q = RNFree X H ⧸ N`, where `N` contains the commutation and splitting relators.
* `rnNF_split_one`: one splitting relator, conjugated by `e : cone [x₀] → cone w`, rewrites
  `rfConjL e k` as `rfV s * Π_x rfConjL (e * E_x) (k|_x)` over the cones `w ++ [x]`.  Here
  `s = e * shift * e⁻¹` fixes every stream outside `cone w`.
* `rnNF_split_deep`: after `n` rounds (`rnNF_combine`), all words have the form `w ++ r` with
  `|r| = n`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X] [Nontrivial X]

/-- One splitting step on a conjugated factor. -/
theorem rnNF_split_one (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hsplit : nfSplitRelators H x₀ ⊆ N)
    (e : ↥(higmanThompsonV X)) (w : List X) (k : ↥H)
    (he : MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w) :
    ∃ (s : ↥(higmanThompsonV X)) (P' : List (↥(higmanThompsonV X) × List X × ↥H)),
      (∀ z, ¬ IsStreamPrefix w z → (s : Equiv.Perm (Cantor X)) z = z) ∧
      (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
      P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
      (∀ a ∈ P', ∃ x, a.2.1 = w ++ [x]) ∧
      rfConjL H N e k = rfV H N s * (P'.map fun a => rfConjL H N a.1 a.2.2).prod := by
  obtain ⟨l, hl, hall⟩ := rcore_exists_list (X := X)
  refine ⟨e * rcoreShift [x₀] (TreeAut.rootPerm (k : TreeAut X)) * e⁻¹,
    l.map fun x => (e * rcoreE x₀ [x₀, x], w ++ [x], rcoreSt H hH k x),
    fun z hz => ?_, fun a ha => ?_, ?_, fun a ha => ?_, ?_⟩
  · have hz' : ¬ IsStreamPrefix [x₀] ((e : Equiv.Perm (Cantor X))⁻¹ z) := by
      intro h0
      apply hz
      have h1 := prepend_dropN_of_isStreamPrefix _ _ h0
      have h2 : z = prepend w (dropN [x₀].length ((e : Equiv.Perm (Cantor X))⁻¹ z)) := by
        rw [← he, h1, Equiv.Perm.apply_inv_self]
      rw [h2]
      exact isStreamPrefix_prepend _ _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply,
      show ((rcoreShift [x₀] (TreeAut.rootPerm (k : TreeAut X)) : ↥(higmanThompsonV X)) :
          Equiv.Perm (Cantor X)) =
        localize [x₀] (nfRootShift (TreeAut.rootPerm (k : TreeAut X))) from rfl,
      localize_apply_of_not hz', Equiv.Perm.apply_inv_self]
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
    exact (rcoreE_spec x₀ (List.cons_ne_nil x₀ [x])).comp (he.append [x])
  · rw [List.pairwise_map]
    exact hl.pairwise_of_forall_ne fun a _ b _ hab =>
      rnNF_incomp_of_length (by simp) fun h => hab (by simpa using h)
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
    exact ⟨x, rfl⟩
  · have hprod : ((l.map fun x => (e * rcoreE x₀ [x₀, x], w ++ [x], rcoreSt H hH k x)).map
        fun a => rfConjL H N a.1 a.2.2).prod =
        rfV H N e * (l.map fun x => rfConjL H N (rcoreE x₀ [x₀, x]) (rcoreSt H hH k x)).prod *
          (rfV H N e)⁻¹ := by
      rw [rnNF_conj_prod, List.map_map]
      refine congrArg List.prod (List.map_congr_left fun x _ => ?_)
      exact (rcore_conj_rfConjL H N e (rcoreE x₀ [x₀, x]) (rcoreSt H hH k x)).symm
    rw [rcore_rfConjL_eq H N e k, rnKer_rfL_split H N hH x₀ hsplit hl hall k, hprod,
      map_mul (rfV H N) (e * _) e⁻¹, map_mul (rfV H N) e, map_inv]
    simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_split_one

/-- Splitting a conjugated factor `n` times. -/
theorem rnNF_split_deep (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hsplit : nfSplitRelators H x₀ ⊆ N) (n : ℕ) :
    ∀ (e : ↥(higmanThompsonV X)) (w : List X) (k : ↥H),
      MapsCone (e : Equiv.Perm (Cantor X)) [x₀] w →
      ∃ (s : ↥(higmanThompsonV X)) (P' : List (↥(higmanThompsonV X) × List X × ↥H)),
        (∀ z, ¬ IsStreamPrefix w z → (s : Equiv.Perm (Cantor X)) z = z) ∧
        (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
        P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
        (∀ a ∈ P', w <+: a.2.1 ∧ a.2.1.length = w.length + n) ∧
        rfConjL H N e k = rfV H N s * (P'.map fun a => rfConjL H N a.1 a.2.2).prod := by
  induction n with
  | zero =>
    intro e w k he
    refine ⟨1, [(e, w, k)], fun _ _ => rfl, fun a ha => ?_, List.pairwise_singleton _ _,
      fun a ha => ?_, ?_⟩
    · obtain rfl := List.mem_singleton.mp ha
      exact he
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨List.prefix_refl w, rfl⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_one, one_mul,
        mul_one]
  | succ n ih =>
    intro e w k he
    obtain ⟨s, P', hs, hv, hp, hw, heq⟩ := ih e w k he
    obtain ⟨s₁, P'', hs₁, hv'', hp'', hw'', heq''⟩ :=
      rnNF_combine H N x₀ hcomm (fun u => u.length = w.length + (n + 1)) P' hv hp
        fun a ha => by
          obtain ⟨sa, Pa, hsa, hva, hpa, hwa, hea⟩ :=
            rnNF_split_one H N hH x₀ hsplit a.1 a.2.1 a.2.2 (hv a ha)
          refine ⟨sa, Pa, hsa, hva, hpa, fun b hb => ?_, hea⟩
          obtain ⟨x, hx⟩ := hwa b hb
          have hlen := (hw a ha).2
          show a.2.1 <+: b.2.1 ∧ b.2.1.length = w.length + (n + 1)
          rw [hx, List.length_append, List.length_singleton]
          exact ⟨List.prefix_append _ _, by omega⟩
    refine ⟨s * s₁, P'', fun z hz => ?_, hv'', hp'', fun b hb => ?_, ?_⟩
    · rw [Subgroup.coe_mul, Equiv.Perm.mul_apply,
        hs₁ z fun a ha h => hz (IsStreamPrefix.of_prefix (hw a ha).1 h), hs z hz]
    · obtain ⟨⟨a, ha, hab⟩, hR⟩ := hw'' b hb
      exact ⟨(hw a ha).1.trans hab, hR⟩
    · rw [heq, heq'', map_mul (rfV H N) s s₁, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_split_deep

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
