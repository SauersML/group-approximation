import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFullArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketArcTrim
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.Meta.AxiomGuard

/-!
# First-turn order forces a proper source arc

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Let the source arc `t_1 = a_1 … a_n` be the whole boundary of the source
cell, so the face rotation takes `a_n` to `a_1`.  The reversed arc `α a_n … α a_1` lies on the
boundary cycle.  The turn into its first dart `α a_n` rotates from `α a_n`; one rotation step gives
`σ (α a_n) = a_1`, a dart on an edge of the cycle, since `α a_1` lies on the cycle.  In first-turn
order a turn passes only darts off the edges of the cycle, so the turn has length one, and the dart
before `α a_n` is `α a_1`.  That dart ends the reversed arc, while the dart before the reversed arc
lies on a side or on the target arc, and the cycle has no repeated darts.

So a pocket in first-turn order whose cycle holds anything besides the reversed source arc has a
proper source arc (a finding of lane `ms-intro-4`, formalized here).

* `PocketFullArc.rel_of_isChain_append`: a chain relates the last entry of a prefix to the first
  entry of the rest.
* `PocketFaceSet.sourceArc_lt_of_firstTurns`: first-turn order and a nonempty remainder give a proper
  source arc.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace PocketFullArc

/-- **A chain across a split** relates the last entry of the prefix to the first entry of the
rest. -/
theorem rel_of_isChain_append {α : Type*} {R : α → α → Prop} {l l₁ l₂ : List α}
    (hl : l = l₁ ++ l₂) (h : l.IsChain R) : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y := by
  subst hl
  exact (List.isChain_append.mp h).2.2

end PocketFullArc

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **First-turn order forces a proper source arc**, when the cycle holds a dart off the reversed
source arc. -/
theorem sourceArc_lt_of_firstTurns (K : PocketFaceSet D eps X lo hi) (hK : K.FirstTurns)
    (hrest : K.firstSide ++ K.secondSide ++ K.targetArc.darts ≠ []) :
    K.sourceArc.length < (cellDarts X K.source).length := by
  refine lt_of_le_of_ne K.sourceArc.length_le fun hfull => ?_
  have hne : K.sourceArc.darts ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [CyclicArc.darts_length, hfull]
    exact List.length_pos_iff.mpr (X.faceBoundary (cell X K.source).face).nonempty
  have hlastfirst : X.toCombMap.facePerm (K.sourceArc.darts.getLast hne) =
      K.sourceArc.darts.head hne :=
    K.facePerm_sourceArc_of_full hfull _
      (by rw [List.getLast?_eq_some_getLast hne]; exact Option.mem_some_iff.mpr rfl)
      _ (by rw [List.head?_eq_some_head hne]; exact Option.mem_some_iff.mpr rfl)
  have hσ : X.toCombMap.sigma (X.toCombMap.alpha (K.sourceArc.darts.getLast hne)) =
      K.sourceArc.darts.head hne := hlastfirst
  have hinv : X.toCombMap.alpha (K.sourceArc.darts.head hne) ∈ invDarts X K.sourceArc.darts :=
    List.mem_map_of_mem (List.mem_reverse.mpr (List.head_mem hne))
  have hcyc : X.toCombMap.alpha (K.sourceArc.darts.head hne) ∈ K.boundary.cycle := by
    rw [K.decomposition]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv))
  have hnd := K.boundary.cycle_nodup
  rw [K.decomposition] at hnd
  obtain ⟨hnd₁, -, hdisj₃⟩ := List.nodup_append.mp hnd
  obtain ⟨hnd₂, -, hdisj₂⟩ := List.nodup_append.mp hnd₁
  obtain ⟨-, -, hdisj₁⟩ := List.nodup_append.mp hnd₂
  -- A turn into the first dart of the reversed arc, from a dart `d` off the reversed arc, has
  -- `d = α a_1`.
  have hturn : ∀ d : X.toCombMap.Dart,
      FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
        (X.toCombMap.alpha (X.toCombMap.alpha (K.sourceArc.darts.getLast hne)))
        (X.toCombMap.alpha d) →
      X.toCombMap.alpha (K.sourceArc.darts.head hne) = d := by
    intro d hR
    obtain ⟨k, hk, hke, hkeep⟩ := FirstTurn.reverse_map_alpha_iff.mp hR
    have hk1 : k = 1 := by
      by_contra hk1
      have hx : X.toCombMap.alpha ((X.toCombMap.sigma ^ 1)
          (X.toCombMap.alpha (K.sourceArc.darts.getLast hne))) ∈ K.boundary.cycle := by
        rw [pow_one, hσ]
        exact hcyc
      exact hkeep 1 Nat.one_pos (by omega) (Or.inr hx)
    rw [hk1, pow_one, hσ] at hke
    rw [hke, X.toCombMap.alpha_involutive]
  have hheadInv : X.toCombMap.alpha (K.sourceArc.darts.getLast hne) ∈
      (invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts)).head? := by
    rw [invDarts_eq_getLast_cons hne, List.cons_append, List.head?_cons]
    exact Option.mem_some_iff.mpr rfl
  by_cases hs₁ : K.firstSide = []
  · by_cases hst : K.secondSide ++ K.targetArc.darts = []
    · exact hrest (by rw [hs₁, List.nil_append, hst])
    have hsplit : K.boundary.cycle =
        invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts) := by
      rw [K.decomposition, hs₁, List.nil_append, List.append_assoc]
    have hclose : ∀ x ∈ K.boundary.cycle.getLast?, ∀ y ∈ K.boundary.cycle.head?,
        FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
          (X.toCombMap.alpha y) (X.toCombMap.alpha x) := by
      intro x hx y hy
      rw [List.getLast?_eq_some_getLast K.boundary.cycle_nonempty, Option.mem_some_iff] at hx
      rw [List.head?_eq_some_head K.boundary.cycle_nonempty, Option.mem_some_iff] at hy
      subst hx hy
      exact hK.2
    have happ : invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts) ≠ [] :=
      fun h => hst (List.append_eq_nil_iff.mp h).2
    have hlast : (K.secondSide ++ K.targetArc.darts).getLast hst ∈ K.boundary.cycle.getLast? := by
      rw [hsplit, List.getLast?_eq_some_getLast happ, List.getLast_append_of_ne_nil happ hst]
      exact Option.mem_some_iff.mpr rfl
    have hhead : X.toCombMap.alpha (K.sourceArc.darts.getLast hne) ∈ K.boundary.cycle.head? := by
      rw [hsplit]
      exact hheadInv
    have hd := hturn _ (hclose _ hlast _ hhead)
    rcases List.mem_append.mp (List.getLast_mem hst) with hds₂ | hdt₂
    · exact hdisj₂ _ (List.mem_append_right _ hinv) _ hds₂ hd
    · exact hdisj₃ _ (List.mem_append_left _ (List.mem_append_right _ hinv)) _ hdt₂ hd
  · have hsplit : K.boundary.cycle =
        K.firstSide ++ (invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts)) := by
      rw [K.decomposition, List.append_assoc, List.append_assoc]
    have hd := hturn _ (PocketFullArc.rel_of_isChain_append hsplit hK.1 _
      (by rw [List.getLast?_eq_some_getLast hs₁]; exact Option.mem_some_iff.mpr rfl) _ hheadInv)
    exact hdisj₁ _ (List.getLast_mem hs₁) _ hinv hd.symm

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFullArc.rel_of_isChain_append
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.sourceArc_lt_of_firstTurns
