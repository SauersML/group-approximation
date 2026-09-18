import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsCoreFinal
import GroupApproximation.Meta.AxiomGuard

/-!
# Local copies with trivial deep states lie in the image of `V_X`

Work in `Q = RNFree X H ⧸ N`, where `N` is normal and contains the splitting relators
`nfSplitRelators H x₀`.

* `rnKer_rfL_split`: in `Q`, the local copy `rfL h` equals a shift in `V_X` times the product of
  the local copies of the states `h|_x`, conjugated into the cones `[x₀, x]`.
* `rnKer_rfConjL_mem_range`: if every state of `h` at depth `n` is trivial, then every
  conjugate `rfConjL e h` lies in the range of `rfV`.  Induction on `n`: split once, and every
  factor has trivial states at depth `n - 1`.

These are used in the faithfulness half of the kernel statement
(`EnvelopeRelatorsKernelFinal`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

noncomputable section

variable {X : Type*} [Finite X]

/-- The splitting relator, read in the quotient. -/
theorem rnKer_rfL_split [Nontrivial X] (H : Subgroup (TreeAut X)) (N : Subgroup (RNFree X H))
    [N.Normal] (hH : IsSelfSimilar H) (x₀ : X) (hsplit : nfSplitRelators H x₀ ⊆ N)
    {l : List X} (hl : l.Nodup) (hall : ∀ x, x ∈ l) (h : ↥H) :
    rfL H N h = rfV H N (rcoreShift [x₀] (TreeAut.rootPerm (h : TreeAut X))) *
      (l.map fun x => rfConjL H N (rcoreE x₀ [x₀, x]) (rcoreSt H hH h x)).prod := by
  have hrel : (nfL H h)⁻¹ * nfV H (rcoreShift [x₀] (TreeAut.rootPerm (h : TreeAut X))) *
      (l.map fun x => nfV H (rcoreE x₀ [x₀, x]) * nfL H (rcoreSt H hH h x) *
        (nfV H (rcoreE x₀ [x₀, x]))⁻¹).prod ∈ nfSplitRelators H x₀ :=
    ⟨h, rcoreShift [x₀] (TreeAut.rootPerm (h : TreeAut X)), fun x => rcoreE x₀ [x₀, x],
      rcoreSt H hH h, l, hl, hall, fun _ => rfl,
      fun _ => rcoreE_spec x₀ (List.cons_ne_nil _ _), rfl, rfl⟩
  have h1 := (QuotientGroup.eq_one_iff (N := N) _).mpr (hsplit hrel)
  rw [rcore_mk_relator H N (nfL H h) _ (fun x => rcoreE x₀ [x₀, x]) (rcoreSt H hH h) l,
    mul_assoc] at h1
  rw [rfL_apply]
  exact inv_mul_eq_one.mp h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_rfL_split

/-- The state of `rcoreSt h x` at `t` is the state of `h` at `x :: t`. -/
theorem rnKer_state_rcoreSt (H : Subgroup (TreeAut X)) (hH : IsSelfSimilar H) (h : ↥H) (x : X)
    (t : List X) :
    TreeAut.state ((rcoreSt H hH h x : ↥H) : TreeAut X) t =
      TreeAut.state (h : TreeAut X) (x :: t) :=
  (TreeAut.state_append (h : TreeAut X) [x] t).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_state_rcoreSt

/-- If all states of `h` at depth `n` are trivial, every conjugated local copy of `h` lies in
the image of `V_X`. -/
theorem rnKer_rfConjL_mem_range [Nontrivial X] (H : Subgroup (TreeAut X))
    (N : Subgroup (RNFree X H)) [N.Normal] (hH : IsSelfSimilar H) (x₀ : X)
    (hsplit : nfSplitRelators H x₀ ⊆ N) (n : ℕ) :
    ∀ h : ↥H, (∀ t : List X, t.length = n → TreeAut.state (h : TreeAut X) t = 1) →
      ∀ e : ↥(higmanThompsonV X), rfConjL H N e h ∈ (rfV H N).range := by
  obtain ⟨l, hl, hall⟩ := rcore_exists_list (X := X)
  induction n with
  | zero =>
    intro h hh e
    have h1 : h = 1 := by
      apply Subtype.ext
      have h0 := hh [] rfl
      rw [TreeAut.state_nil] at h0
      exact h0
    rw [h1, map_one]
    exact Subgroup.one_mem _
  | succ n ih =>
    intro h hh e
    rw [rcore_rfConjL_eq, rnKer_rfL_split H N hH x₀ hsplit hl hall h]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (MonoidHom.mem_range.mpr ⟨e, rfl⟩)
      (Subgroup.mul_mem _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
        (Subgroup.list_prod_mem _ fun y hy => ?_)))
      (Subgroup.inv_mem _ (MonoidHom.mem_range.mpr ⟨e, rfl⟩))
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
    refine ih (rcoreSt H hH h x) (fun t ht => ?_) (rcoreE x₀ [x₀, x])
    rw [rnKer_state_rcoreSt]
    exact hh (x :: t) (by rw [List.length_cons, ht])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnKer_rfConjL_mem_range

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
