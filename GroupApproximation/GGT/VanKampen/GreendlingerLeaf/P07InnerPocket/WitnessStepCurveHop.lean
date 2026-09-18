import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusSplit
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeMirror
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeFirstReturn
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-66: hops, bounce chains and the mirror successor

Lane gl-p07-66.  Certifies no printed sentence on its own.  NOT COMPILED: authored without
running Lean.

Fix a combinatorial map `M` and a list `Γ` of darts.
* `Hop u v`: some `σ ^ m u = v` with `0 < m`, and every strictly intermediate `σ ^ k u` has
  itself and its reverse off `Γ`.
* `Rel x y`: if `x ∈ Γ` then `Hop (α x) y`, and if `x ∉ Γ` then `Hop x y`.

Math.
1. Hops compose through a *bounce* dart `z` (`z ∉ Γ`, `α z ∉ Γ`): the iterate at the junction
   is `z` itself, which is allowed as an intermediate.  So `Rel x z → Rel z y → Rel x y`.
2. A chain for `Rel` survives deleting bounce darts (`witnessStepCurve_chain_filter`).
3. If `Γ ++ Γ` is a `Rel` chain, every cyclic step `(x, y)` of the inverse word
   `w = Γ.reverse.map α` is a successor step of the mirror `(α, σ⁻¹)` relative to `w`.
   Indeed `(x, y)` is consecutive in `w ++ w = (Γ ++ Γ).reverse.map α`, so `(α y, α x)` is
   consecutive in `Γ ++ Γ`.  As `α y ∈ Γ`, `Rel (α y) (α x)` gives `Hop y (α x)`:
   `σ ^ m y = α x`.  Then `σ⁻¹ ^ m (α x) = y`, and the intermediate `σ⁻¹ ^ k (α x)` is
   `σ ^ (m - k) y`, which with its reverse is off `Γ`, i.e. off `w`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

namespace FourPieceWitness

/-- A run of vertex rotations from `u` to `v` whose strict intermediates are off `Γ` together
with their reverses. -/
def witnessStepCurve_Hop (M : CombMap.{u}) (Γ : List M.Dart) (u v : M.Dart) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (M.sigma ^ m) u = v ∧
    ∀ k : ℕ, 0 < k → k < m → (M.sigma ^ k) u ∉ Γ ∧ M.alpha ((M.sigma ^ k) u) ∉ Γ

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_Hop

/-- The step relation of the bounce chain: kept darts turn from their reverse, bounce darts
turn from themselves. -/
def witnessStepCurve_Rel (M : CombMap.{u}) (Γ : List M.Dart) (x y : M.Dart) : Prop :=
  (x ∈ Γ → witnessStepCurve_Hop M Γ (M.alpha x) y) ∧ (x ∉ Γ → witnessStepCurve_Hop M Γ x y)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_Rel

/-- **Hops compose through a bounce dart.** -/
theorem witnessStepCurve_hop_trans {M : CombMap.{u}} {Γ : List M.Dart} {x y z : M.Dart}
    (h₁ : witnessStepCurve_Hop M Γ x z) (h₂ : witnessStepCurve_Hop M Γ z y) (hz : z ∉ Γ)
    (hz' : M.alpha z ∉ Γ) : witnessStepCurve_Hop M Γ x y := by
  obtain ⟨m₁, hm₁, hx, hn₁⟩ := h₁
  obtain ⟨m₂, hm₂, hzy, hn₂⟩ := h₂
  have hsplit : ∀ r : ℕ, (M.sigma ^ (m₁ + r)) x = (M.sigma ^ r) z := by
    intro r
    rw [add_comm, pow_add, Equiv.Perm.mul_apply, hx]
  refine ⟨m₁ + m₂, by omega, by rw [hsplit, hzy], ?_⟩
  intro k hk hkm
  rcases lt_trichotomy k m₁ with hlt | heq | hgt
  · exact hn₁ k hk hlt
  · rw [heq, hx]
    exact ⟨hz, hz'⟩
  · obtain ⟨r, rfl⟩ : ∃ r, k = m₁ + r := ⟨k - m₁, by omega⟩
    rw [hsplit]
    exact hn₂ r (by omega) (by omega)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_hop_trans

/-- **The step relation composes through a bounce dart.** -/
theorem witnessStepCurve_rel_trans {M : CombMap.{u}} {Γ : List M.Dart} {x y z : M.Dart}
    (h₁ : witnessStepCurve_Rel M Γ x z) (h₂ : witnessStepCurve_Rel M Γ z y) (hz : z ∉ Γ)
    (hz' : M.alpha z ∉ Γ) : witnessStepCurve_Rel M Γ x y := by
  obtain ⟨h₁a, h₁b⟩ := h₁
  obtain ⟨-, h₂b⟩ := h₂
  exact ⟨fun hx => witnessStepCurve_hop_trans (h₁a hx) (h₂b hz) hz hz',
    fun hx => witnessStepCurve_hop_trans (h₁b hx) (h₂b hz) hz hz'⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_rel_trans

/-- **A run of kept darts between two turns is a chain of the step relation.**  The head `e`
turns like `α u`; the inner darts `L` are kept, so each turns from its reverse. -/
theorem witnessStepCurve_rel_segment {M : CombMap.{u}} {Γ : List M.Dart} {v : M.Dart} :
    ∀ (L : List M.Dart) (u e : M.Dart),
      (u :: (L ++ [v])).IsChain (fun p q => witnessStepCurve_Hop M Γ (M.alpha p) q) →
      (∀ q, witnessStepCurve_Hop M Γ (M.alpha u) q → witnessStepCurve_Rel M Γ e q) →
      (∀ d ∈ L, d ∈ Γ) → (e :: (L ++ [v])).IsChain (witnessStepCurve_Rel M Γ) := by
  intro L
  induction L with
  | nil =>
    intro u e h he _
    simp only [List.nil_append, List.isChain_cons_cons] at h ⊢
    exact ⟨he v h.1, List.IsChain.singleton v⟩
  | cons l L ih =>
    intro u e h he hL
    simp only [List.cons_append, List.isChain_cons_cons] at h ⊢
    have hl : l ∈ Γ := hL l List.mem_cons_self
    refine ⟨he l h.1, ih l l h.2 (fun q hq => ⟨fun _ => hq, fun hl' => absurd hl hl'⟩) ?_⟩
    exact fun d hd => hL d (List.mem_cons_of_mem l hd)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_rel_segment

/-- The head of a segment that starts at a bounce dart `α u` turns like `α u`. -/
theorem witnessStepCurve_rel_of_bounce {M : CombMap.{u}} {Γ : List M.Dart} {u : M.Dart}
    (hu : M.alpha u ∉ Γ) :
    ∀ q, witnessStepCurve_Hop M Γ (M.alpha u) q → witnessStepCurve_Rel M Γ (M.alpha u) q :=
  fun _ hq => ⟨fun h => absurd h hu, fun _ => hq⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_rel_of_bounce

/-- **Gluing two chains at a common dart.** -/
theorem witnessStepCurve_chain_glue {β : Type*} {R : β → β → Prop} {y : β} {L₂ : List β} :
    ∀ (L₁ : List β) (x : β), (x :: (L₁ ++ [y])).IsChain R → (y :: L₂).IsChain R →
      (x :: (L₁ ++ y :: L₂)).IsChain R := by
  intro L₁
  induction L₁ with
  | nil =>
    intro x h₁ h₂
    simp only [List.nil_append, List.isChain_cons_cons] at h₁ ⊢
    exact ⟨h₁.1, h₂⟩
  | cons l L ih =>
    intro x h₁ h₂
    simp only [List.cons_append, List.isChain_cons_cons] at h₁ ⊢
    exact ⟨h₁.1, ih l h₁.2 h₂⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_chain_glue

/-- Dropping the last entry of a chain. -/
theorem witnessStepCurve_chain_drop_last {β : Type*} {R : β → β → Prop} {y : β} :
    ∀ (L : List β) (x : β), (x :: (L ++ [y])).IsChain R → (x :: L).IsChain R := by
  intro L
  induction L with
  | nil => exact fun x _ => List.IsChain.singleton x
  | cons l L ih =>
    intro x h
    simp only [List.cons_append, List.isChain_cons_cons] at h ⊢
    exact ⟨h.1, ih l h.2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_chain_drop_last

/-- **A closed chain doubles.** -/
theorem witnessStepCurve_chain_double {β : Type*} {R : β → β → Prop} {v : β} {L : List β}
    (h : (v :: (L ++ [v])).IsChain R) : (v :: (L ++ v :: L)).IsChain R :=
  witnessStepCurve_chain_glue L v h (witnessStepCurve_chain_drop_last L v h)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepCurve_chain_double

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
