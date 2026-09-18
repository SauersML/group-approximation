import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormMerge
import GroupApproximation.Meta.AxiomGuard

/-!
# The normal-form lemma

`RNNFStep H N x₀ g` says that right multiplication by `g` maps normal forms
`rfV v * Π P` to normal forms.  Such `g` are closed under products (`rnNF_step_mul`).  Every
generator of `RNFree X H` has this property:
* `rfV u`: `rnNF_mul_rfV`.
* `rfL k` (step C): deepen `P` to words of length `M`.  Split `rfL k` into factors on words of
  length `M`, with the shift on the right.  Merge the two lists, whose words are pairwise equal
  or incomparable, then absorb the shift with step B.
* `rfConjL e k = rfV e * rfL k * rfV e⁻¹`, and hence any product of such factors.
* `nfH h`: the root relator writes it as `rfV a * Π_x rfConjL (E_x) (h|_x)`.

Endpoint: `rnNF_normalForm : RNKerNormalFormStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

/-- Right multiplication by `g` maps normal forms to normal forms. -/
def RNNFStep (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal] (x₀ : X)
    (g : RNFree X H ⧸ N) : Prop :=
  ∀ (v : ↥(higmanThompsonV X)) (P : List (↥(higmanThompsonV X) × List X × ↥H)),
    (∀ p ∈ P, MapsCone (p.1 : Equiv.Perm (Cantor X)) [x₀] p.2.1) →
    P.Pairwise (fun p p' => ¬ p.2.1 <+: p'.2.1 ∧ ¬ p'.2.1 <+: p.2.1) →
    ∃ (v' : ↥(higmanThompsonV X)) (P' : List (↥(higmanThompsonV X) × List X × ↥H)),
      (∀ a ∈ P', MapsCone (a.1 : Equiv.Perm (Cantor X)) [x₀] a.2.1) ∧
      P'.Pairwise (fun a a' => ¬ a.2.1 <+: a'.2.1 ∧ ¬ a'.2.1 <+: a.2.1) ∧
      rfV H N v * (P.map fun p => rfConjL H N p.1 p.2.2).prod * g =
        rfV H N v' * (P'.map fun a => rfConjL H N a.1 a.2.2).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RNNFStep

theorem rnNF_step_mul {H : Subgroup (TreeAut X)} {N : Subgroup (RNFree X H)} [N.Normal]
    {x₀ : X} {g₁ g₂ : RNFree X H ⧸ N} (h₁ : RNNFStep H N x₀ g₁) (h₂ : RNNFStep H N x₀ g₂) :
    RNNFStep H N x₀ (g₁ * g₂) := by
  intro v P hv hp
  obtain ⟨v₁, P₁, hv₁, hp₁, e₁⟩ := h₁ v P hv hp
  obtain ⟨v₂, P₂, hv₂, hp₂, e₂⟩ := h₂ v₁ P₁ hv₁ hp₁
  exact ⟨v₂, P₂, hv₂, hp₂, by rw [← mul_assoc, e₁, e₂]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_step_mul

variable [Nontrivial X]

/-- **Step C.** Right multiplication by `rfL k` keeps the normal form. -/
theorem rnNF_mul_rfL (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) (hsplit : nfSplitRelators H x₀ ⊆ N) (k : ↥H) :
    RNNFStep H N x₀ (rfL H N k) := by
  intro v P hv hpair
  obtain ⟨B, hB⟩ := rnNF_exists_bound
    (fun p : ↥(higmanThompsonV X) × List X × ↥H => p.2.1.length) P
  obtain ⟨s, P₁, hv₁, hp₁, hl₁, he₁⟩ := rnNF_deepen H N hH x₀ hcomm hsplit (B + 1) P hv hpair
    fun p hp => Nat.le_succ_of_le (hB p hp)
  obtain ⟨t, Q, hvQ, hpQ, hwQ, heQ⟩ :=
    rnNF_split_right H N hH x₀ hcomm hsplit B 1 [x₀] k (mapsCone_one [x₀])
  obtain ⟨P₂, hv₂, hp₂, he₂⟩ := rnNF_merge H N x₀ hcomm hdisj Q hvQ hpQ P₁ hv₁ hp₁
    fun p hp q hq => by
      refine (Classical.em (p.2.1 = q.2.1)).elim Or.inl fun hne =>
        Or.inr (rnNF_incomp_of_length ?_ hne)
      have h1 := (hwQ q hq).2
      have h2 := hl₁ p hp
      rw [List.length_singleton] at h1
      omega
  obtain ⟨v', P'', hv'', hp'', he''⟩ :=
    rnNF_mul_rfV H N hH x₀ hcomm hsplit (v * s) P₂ hv₂ hp₂ t
  have hL : rfL H N k = rfConjL H N 1 k := by
    rw [rcore_rfConjL_eq H N 1 k, map_one, one_mul, inv_one, mul_one]
  refine ⟨v', P'', hv'', hp'', ?_⟩
  rw [← he'', ← he₂, hL, heQ, he₁, map_mul]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_mul_rfL

/-- Right multiplication by a conjugated factor keeps the normal form. -/
theorem rnNF_mul_rfConjL (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) (hsplit : nfSplitRelators H x₀ ⊆ N)
    (e : ↥(higmanThompsonV X)) (k : ↥H) : RNNFStep H N x₀ (rfConjL H N e k) := by
  intro v P hv hpair
  obtain ⟨v₁, P₁, hv₁, hp₁, h₁⟩ := rnNF_mul_rfV H N hH x₀ hcomm hsplit v P hv hpair e
  obtain ⟨v₂, P₂, hv₂, hp₂, h₂⟩ := rnNF_mul_rfL H N hH x₀ hcomm hdisj hsplit k v₁ P₁ hv₁ hp₁
  obtain ⟨v₃, P₃, hv₃, hp₃, h₃⟩ := rnNF_mul_rfV H N hH x₀ hcomm hsplit v₂ P₂ hv₂ hp₂ e⁻¹
  refine ⟨v₃, P₃, hv₃, hp₃, ?_⟩
  rw [rcore_rfConjL_eq H N e k, ← map_inv (rfV H N) e, ← h₃, ← h₂, ← h₁]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_mul_rfConjL

/-- Right multiplication by a product of conjugated factors keeps the normal form. -/
theorem rnNF_mul_prod (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hcomm : nfCommRelators H x₀ ⊆ N)
    (hdisj : nfDisjRelators H x₀ ⊆ N) (hsplit : nfSplitRelators H x₀ ⊆ N) {ι : Type*}
    (c : ι → ↥(higmanThompsonV X)) (k : ι → ↥H) (l : List ι) :
    RNNFStep H N x₀ (l.map fun x => rfConjL H N (c x) (k x)).prod := by
  induction l with
  | nil =>
    intro v P hv hp
    exact ⟨v, P, hv, hp, by simp only [List.map_nil, List.prod_nil, mul_one]⟩
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons]
    exact rnNF_step_mul (rnNF_mul_rfConjL H N hH x₀ hcomm hdisj hsplit (c x) (k x)) ih

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_mul_prod

/-- The root relator writes `nfH h` as a shift times a product of conjugated factors. -/
theorem rnNF_mk_nfH (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H)) [N.Normal]
    (hH : IsSelfSimilar H) (x₀ : X) (hroot : nfRootRelators H x₀ ⊆ N) {l : List X}
    (hl : l.Nodup) (hall : ∀ x, x ∈ l) (h : ↥H) :
    ((nfH H h : RNFree X H) : RNFree X H ⧸ N) =
      rfV H N (rcoreShift [] (TreeAut.rootPerm (h : TreeAut X))) *
        (l.map fun x => rfConjL H N (rcoreE x₀ [x]) (rcoreSt H hH h x)).prod := by
  have hrel : (nfH H h)⁻¹ * nfV H (rcoreShift [] (TreeAut.rootPerm (h : TreeAut X))) *
      (l.map fun x => nfV H (rcoreE x₀ [x]) * nfL H (rcoreSt H hH h x) *
        (nfV H (rcoreE x₀ [x]))⁻¹).prod ∈ nfRootRelators H x₀ :=
    ⟨h, rcoreShift [] (TreeAut.rootPerm (h : TreeAut X)), fun x => rcoreE x₀ [x],
      rcoreSt H hH h, l, hl, hall, fun _ => rfl,
      fun x => rcoreE_spec x₀ (List.cons_ne_nil x []),
      localize_nil (nfRootShift (TreeAut.rootPerm (h : TreeAut X))), rfl⟩
  have h1 := (QuotientGroup.eq_one_iff (N := N) _).mpr (hroot hrel)
  rw [rcore_mk_relator H N (nfH H h) _ (fun x => rcoreE x₀ [x]) (rcoreSt H hH h) l,
    mul_assoc] at h1
  exact inv_mul_eq_one.mp h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnNF_mk_nfH

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
