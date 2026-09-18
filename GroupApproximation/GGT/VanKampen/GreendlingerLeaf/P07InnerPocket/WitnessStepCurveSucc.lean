import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepCurveHop
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: from a doubled bounce chain to the mirror successor

Lane gl-p07-66.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

Math.
* Deleting darts `y` with `Q y` from a chain of a relation that composes through such darts
  keeps a chain (`witnessStepCurve_chain_filter`).
* A cyclic step `(x, y)` of `l` (a step of some rotation) is a step of `l ++ l`.
* If `L.reverse.map f = s ++ x :: y :: t` for an involution `f`, then `(f y, f x)` is a step
  of `L`.
* `witnessStepCurve_succ_of_chain`: if `Γ ++ Γ` is a chain of `witnessStepCurve_Rel M Γ`, every
  cyclic step `(x, y)` of `w = Γ.reverse.map α` is a successor step of the mirror relative to
  `w`.  The step `(α y, α x)` of `Γ ++ Γ` has `α y ∈ Γ`, so it is `Hop y (α x)`:
  `σ ^ m y = α x`, whence `σ⁻¹ ^ m (α x) = y` and `σ⁻¹ ^ k (α x) = σ ^ (m - k) y` for `k ≤ m`.
  A dart `e` is in `w` iff `α e ∈ Γ`; the hop keeps the intermediates and their reverses
  off `Γ`, hence off `w`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

namespace FourPieceWitness

/-- **Deleting composable darts after the head of a chain.** -/
theorem witnessStepCurve_chain_cons_filter {β : Type*} {R : β → β → Prop} (p : β → Bool)
    (Q : β → Prop) (htrans : ∀ x y z, R x y → R y z → Q y → R x z) :
    ∀ (L : List β) (x : β), (x :: L).IsChain R → (∀ y ∈ L, p y = false → Q y) →
      (x :: L.filter p).IsChain R := by
  intro L
  induction L with
  | nil =>
    intro x h _
    rw [List.filter_nil]
    exact h
  | cons y L ih =>
    intro x h hQ
    have hQ' : ∀ z ∈ L, p z = false → Q z := fun z hz => hQ z (List.mem_cons_of_mem y hz)
    rw [List.isChain_cons_cons] at h
    by_cases hp : p y = true
    · rw [List.filter_cons_of_pos hp, List.isChain_cons_cons]
      exact ⟨h.1, ih y h.2 hQ'⟩
    · rw [List.filter_cons_of_neg hp]
      have hy : Q y := hQ y List.mem_cons_self (by simpa using hp)
      refine ih x ?_ hQ'
      cases L with
      | nil => exact List.IsChain.singleton x
      | cons z L' =>
        rw [List.isChain_cons_cons] at h ⊢
        exact ⟨htrans x y z h.1 h.2.1 hy, h.2.2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_chain_cons_filter

/-- **Deleting composable darts from a chain.** -/
theorem witnessStepCurve_chain_filter {β : Type*} {R : β → β → Prop} (p : β → Bool)
    (Q : β → Prop) (htrans : ∀ x y z, R x y → R y z → Q y → R x z) :
    ∀ L : List β, L.IsChain R → (∀ y ∈ L, p y = false → Q y) → (L.filter p).IsChain R := by
  intro L
  induction L with
  | nil =>
    intro _ _
    rw [List.filter_nil]
    exact List.IsChain.nil
  | cons y L ih =>
    intro h hQ
    have hQ' : ∀ z ∈ L, p z = false → Q z := fun z hz => hQ z (List.mem_cons_of_mem y hz)
    by_cases hp : p y = true
    · rw [List.filter_cons_of_pos hp]
      exact witnessStepCurve_chain_cons_filter p Q htrans L y h hQ'
    · rw [List.filter_cons_of_neg hp]
      exact ih h.tail hQ'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_chain_filter

/-- **A cyclic step of a list is a step of the doubled list.** -/
theorem witnessStepCurve_append_self_of_rotate {β : Type*} {l s t : List β} {x y : β} {n : ℕ}
    (h : l.rotate n = s ++ x :: y :: t) : ∃ s' t', l ++ l = s' ++ x :: y :: t' := by
  rw [List.rotate_eq_drop_append_take_mod] at h
  refine ⟨l.take (n % l.length) ++ s, t ++ l.drop (n % l.length), ?_⟩
  have e : l ++ l = l.take (n % l.length) ++ (l.drop (n % l.length) ++
      l.take (n % l.length)) ++ l.drop (n % l.length) := by
    rw [List.append_assoc, List.append_assoc, List.take_append_drop, ← List.append_assoc,
      List.take_append_drop]
  rw [e, h]
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_append_self_of_rotate

/-- **A step of a reversed image under an involution.** -/
theorem witnessStepCurve_pair_of_reverse_map {β : Type*} {f : β → β} (hf : Function.Involutive f)
    {L s t : List β} {x y : β} (h : L.reverse.map f = s ++ x :: y :: t) :
    ∃ s' t', L = s' ++ f y :: f x :: t' := by
  refine ⟨(t.map f).reverse, (s.map f).reverse, ?_⟩
  have key : ∀ l : List β, (l.map f).map f = l := fun l => by
    rw [List.map_map, hf.comp_self, List.map_id]
  have hL : L = ((L.reverse.map f).map f).reverse := by
    rw [key, List.reverse_reverse]
  rw [hL, h]
  simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_pair_of_reverse_map

/-- **A hop from `y` to `α x` is a mirror successor step from `x` to `y`** relative to the
inverse word `Γ.reverse.map α`. -/
theorem witnessStepCurve_succ_of_hop {M : CombMap.{u}} {Γ : List M.Dart} {x y : M.Dart}
    (h : witnessStepCurve_Hop M Γ y (M.alpha x)) :
    WitnessStepGenusSucc (witnessStepBridge_mirror M) (Γ.reverse.map M.alpha) x y := by
  obtain ⟨m, hm, hσ, hnot⟩ := h
  have hmem : ∀ z, z ∈ Γ.reverse.map M.alpha ↔ M.alpha z ∈ Γ := by
    intro z
    constructor
    · intro hz
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
      rw [M.alpha_involutive e]
      exact List.mem_reverse.mp he
    · intro hz
      exact List.mem_map.mpr ⟨M.alpha z, List.mem_reverse.mpr hz, M.alpha_involutive z⟩
  refine ⟨m, hm, ?_, ?_⟩
  · change (M.sigma⁻¹ ^ m) (M.alpha x) = y
    rw [← hσ, inv_pow]
    exact Equiv.Perm.inv_eq_iff_eq.mpr rfl
  · intro k hk hkm
    show (M.sigma⁻¹ ^ k) (M.alpha x) ∉ Γ.reverse.map M.alpha ∧
      M.alpha ((M.sigma⁻¹ ^ k) (M.alpha x)) ∉ Γ.reverse.map M.alpha
    obtain ⟨r, rfl⟩ : ∃ r, m = k + r := ⟨m - k, by omega⟩
    have hval : (M.sigma⁻¹ ^ k) (M.alpha x) = (M.sigma ^ r) y := by
      rw [← hσ, witnessStepBridge_inv_pow_apply]
    rw [hval, hmem, hmem, M.alpha_involutive ((M.sigma ^ r) y)]
    have hr := hnot r (by omega) (by omega)
    exact ⟨hr.2, hr.1⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_succ_of_hop

/-- **A doubled bounce chain makes the inverse word a cyclic mirror successor walk.** -/
theorem witnessStepCurve_succ_of_chain {M : CombMap.{u}} {Γ : List M.Dart}
    (hc : (Γ ++ Γ).IsChain (witnessStepCurve_Rel M Γ)) {n : ℕ} {s t : List M.Dart}
    {x y : M.Dart} (h : (Γ.reverse.map M.alpha).rotate n = s ++ x :: y :: t) :
    WitnessStepGenusSucc (witnessStepBridge_mirror M) (Γ.reverse.map M.alpha) x y := by
  obtain ⟨s₁, t₁, h₁⟩ := witnessStepCurve_append_self_of_rotate h
  have h₂ : (Γ ++ Γ).reverse.map M.alpha = s₁ ++ x :: y :: t₁ := by
    rw [← h₁, List.reverse_append, List.map_append]
  obtain ⟨s₂, t₂, h₃⟩ := witnessStepCurve_pair_of_reverse_map M.alpha_involutive h₂
  have hrel := List.isChain_iff_forall_rel_of_append_cons_cons.mp hc h₃
  have hy : M.alpha y ∈ Γ := by
    have hmem : M.alpha y ∈ Γ ++ Γ := by
      rw [h₃]
      simp
    rw [List.mem_append, or_self] at hmem
    exact hmem
  unfold witnessStepCurve_Rel at hrel
  have hop := hrel.1 hy
  rw [M.alpha_involutive y] at hop
  exact witnessStepCurve_succ_of_hop hop

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_succ_of_chain

/-- **The filter of the four bounce blocks.** -/
theorem witnessStepCurve_filter_four {β : Type*} (p : β → Bool) {B G₂ A G₁ : List β}
    {z₂ z₃ z₄ : β} (hB : ∀ d ∈ B, p d = true) (h₂ : ¬ p z₂ = true)
    (hG₂ : ∀ d ∈ G₂, p d = true) (h₃ : ¬ p z₃ = true) (hA : ∀ d ∈ A, p d = true)
    (h₄ : ¬ p z₄ = true) (hG₁ : ∀ d ∈ G₁, p d = true) :
    (B ++ z₂ :: (G₂ ++ z₃ :: (A ++ z₄ :: G₁))).filter p = B ++ G₂ ++ A ++ G₁ := by
  rw [List.filter_append, List.filter_eq_self.mpr hB, List.filter_cons_of_neg h₂,
    List.filter_append, List.filter_eq_self.mpr hG₂, List.filter_cons_of_neg h₃,
    List.filter_append, List.filter_eq_self.mpr hA, List.filter_cons_of_neg h₄,
    List.filter_eq_self.mpr hG₁]
  simp only [List.append_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_filter_four

/-- **The filter of a doubled closed list.** -/
theorem witnessStepCurve_filter_double {β : Type*} (p : β → Bool) {z : β} {L Γ : List β}
    (hz : ¬ p z = true) (hL : L.filter p = Γ) : (z :: (L ++ z :: L)).filter p = Γ ++ Γ := by
  rw [List.filter_cons_of_neg hz, List.filter_append, List.filter_cons_of_neg hz, hL]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_filter_double

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
