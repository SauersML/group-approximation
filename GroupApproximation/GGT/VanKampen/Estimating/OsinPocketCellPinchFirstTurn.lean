import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSplit
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch step between two cells, for a pocket in first-turn order

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

The cell analogue of `Estimating/OsinPocketPinchFirstTurn.lean` (lane hull-respell, adopted by
ms-intro-4), over its public turn lemmas `PinchFirstTurn.exists_mem_ne_rel_of_isChain` and
`FirstTurn.reverse_map_alpha_iff`, and over the cell splits of
`Estimating/OsinPocketCellPinchSplit.lean`.  At a vertex visited twice, the split at the end of one
turn keeps every turn, keeps first-turn order and lowers the repeated visits.

* `CellPocketFaceSet.FirstTurns`: the cell pocket in first-turn order.  `FirstTurns.closedWalk`
  gives walk order.
* `CellPocketFaceSet.exists_turn_of_not_unpinched`: a pinched cell pocket in first-turn order has a
  turn `d₀ → e₀` with `d₀ ≠ e₀`, and another dart `e` of the cycle at the vertex of `e₀`.
* `CellPocketFaceSet.avoids_of_turn`, `exists_turnInput`: the split at `x = alpha d₀` and the dart
  `y` before `e₀` has both faces inside the face set when the faces of `d₀` and `e₀` are distinct
  G-faces, and every turn of the cycle avoids `x` and `y` before its end.
* `CellPocketFaceSet.firstTurns_pinchSplitInside`, `pinchSplitInside_repeatedVisits_lt_of_turn`.
* `CellPocketFaceSet.GoodCorners`, `CellPocketPinchGoodCornerStepStatement`,
  `cellPocketPinchGoodCornerStep`: one step of the cell pinch for a pinched cell pocket in first-turn
  order whose boundary darts lie on distinct faces other than relator faces.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

namespace CellPinchFirstTurn

/-- Along a stretch of `p` that meets neither `a` nor `b` before its end, composing with the
transposition of `a` and `b` changes nothing. -/
private theorem mul_swap_pow_apply_of_avoids {α : Type*} [DecidableEq α] (p : Equiv.Perm α)
    (a b d : α) :
    ∀ n : ℕ, (∀ i < n, (p ^ i) d ≠ a ∧ (p ^ i) d ≠ b) →
      ((p * Equiv.swap a b) ^ n) d = (p ^ n) d := by
  intro n
  induction n with
  | zero =>
      intro _
      simp only [pow_zero]
  | succ n ih =>
      intro h
      have hn := h n (Nat.lt_succ_self n)
      rw [pow_succ', Equiv.Perm.mul_apply, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hn.1 hn.2, pow_succ',
        Equiv.Perm.mul_apply]

end CellPinchFirstTurn

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-! ## First-turn order -/

/-- **A cell pocket in first-turn order**: the turn from each dart `d` of the boundary cycle into
the next dart `e`, and from the last dart into the first, rotates from `e` to `alpha d` past darts
off the edges of the cycle. -/
def FirstTurns (K : CellPocketFaceSet D eps X i j) : Prop :=
  K.boundary.cycle.IsChain (fun d e => FirstTurn X.toCombMap
      (K.boundary.cycle.reverse.map X.toCombMap.alpha) (X.toCombMap.alpha e)
      (X.toCombMap.alpha d)) ∧
    FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha (K.boundary.cycle.head K.boundary.cycle_nonempty))
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))

/-- **A cell pocket in first-turn order is in walk order.** -/
theorem FirstTurns.closedWalk {K : CellPocketFaceSet D eps X i j} (hK : K.FirstTurns) :
    K.ClosedWalk := by
  refine ⟨hK.1.imp fun d e h => ?_, ?_⟩
  · have hv := h.vertexOf_eq
    rw [X.toCombMap.alpha_involutive e] at hv
    exact hv.symm
  · have hv := hK.2.vertexOf_eq
    rw [X.toCombMap.alpha_involutive] at hv
    exact hv.symm

/-- The reversal of a dart of the boundary cycle is off the cycle. -/
theorem boundary_alpha_not_mem (K : CellPocketFaceSet D eps X i j) {z : X.toCombMap.Dart}
    (hz : z ∈ K.boundary.cycle) : X.toCombMap.alpha z ∉ K.boundary.cycle := fun haz =>
  ((K.boundary.cycle_mem_iff _).mp hz).2 ((K.boundary.cycle_mem_iff _).mp haz).1

/-- **A pinched cell pocket in first-turn order has a turn into a vertex visited twice.** -/
theorem exists_turn_of_not_unpinched (K : CellPocketFaceSet D eps X i j) (hK : K.FirstTurns)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ∃ d₀ ∈ K.boundary.cycle, ∃ e₀ ∈ K.boundary.cycle, ∃ e ∈ K.boundary.cycle,
      d₀ ≠ e₀ ∧ e ≠ e₀ ∧ X.toCombMap.vertexOf e = X.toCombMap.vertexOf e₀ ∧
        FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
          (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀) := by
  unfold Unpinched at hpinch
  push Not at hpinch
  obtain ⟨a, b, ha, hb, hv, hab⟩ := hpinch
  have ha' := (K.boundary.cycle_mem_iff a).mpr ha
  have hb' := (K.boundary.cycle_mem_iff b).mpr hb
  obtain ⟨d₀, hd₀, hne₀, hturn⟩ := PinchFirstTurn.exists_mem_ne_rel_of_isChain
    K.boundary.cycle_nonempty K.boundary.cycle_nodup hK.1 hK.2 ha' hb' hab
  exact ⟨d₀, hd₀, a, ha', b, hb', hne₀, Ne.symm hab, hv.symm, hturn⟩

/-! ## Turns avoid the split darts -/

/-- **Every turn avoids the split darts before its end.** -/
theorem avoids_of_turn (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) (he₀ : e₀ ∈ K.boundary.cycle)
    (hx : I.x = X.toCombMap.alpha d₀) (hy : X.toCombMap.sigma I.y = e₀)
    {d e : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) (he : e ∈ K.boundary.cycle) {k : ℕ}
    (hk : (X.toCombMap.sigma ^ k) e = X.toCombMap.alpha d)
    (hkeep : ∀ t, 0 < t → t < k →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e)) :
    ∀ i < k, (X.toCombMap.sigma ^ i) e ≠ I.x ∧ (X.toCombMap.sigma ^ i) e ≠ I.y := by
  intro i hi
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hx] at h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [pow_zero, Perm.one_apply] at h
      exact K.boundary_alpha_not_mem hd₀ (by rw [← h]; exact he)
    · refine hkeep i hpos hi (Or.inr ?_)
      rw [h, X.toCombMap.alpha_involutive d₀]
      exact hd₀
  · have h1 : (X.toCombMap.sigma ^ (i + 1)) e = e₀ := by
      rw [pow_succ', Perm.mul_apply, h, hy]
    rcases Nat.lt_or_ge (i + 1) k with hlt | hge
    · exact hkeep (i + 1) (Nat.succ_pos i) hlt (Or.inl (by rw [h1]; exact he₀))
    · obtain rfl : i + 1 = k := by omega
      rw [hk] at h1
      exact K.boundary_alpha_not_mem hd (by rw [h1]; exact he₀)

/-! ## The split at the end of a turn -/

/-- **The split at the end of a turn.**  For a turn `d₀ → e₀` of the boundary cycle whose darts lie
on distinct faces other than relator faces, `x = alpha d₀` and the dart `y` before `e₀` form a pinch
with both faces inside the face set. -/
theorem exists_turnInput [DecidableEq X.toCombMap.Dart] (K : CellPocketFaceSet D eps X i j)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) (he₀ : e₀ ∈ K.boundary.cycle)
    {k₀ : ℕ} (hk₀ : (X.toCombMap.sigma ^ k₀) e₀ = X.toCombMap.alpha d₀)
    (hface : X.toCombMap.faceOf d₀ ≠ X.toCombMap.faceOf e₀)
    (hcell₀ : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf d₀)
    (hcell₁ : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf e₀) :
    ∃ I : PinchSplit.Input X, I.x = X.toCombMap.alpha d₀ ∧ X.toCombMap.sigma I.y = e₀ ∧
      I.Inside K.faces := by
  obtain ⟨y, hy⟩ : ∃ y, X.toCombMap.sigma y = e₀ :=
    ⟨X.toCombMap.sigma.symm e₀, Equiv.apply_symm_apply _ e₀⟩
  obtain ⟨hf₀, -⟩ := (K.boundary.cycle_mem_iff d₀).mp hd₀
  obtain ⟨hf₁, -⟩ := (K.boundary.cycle_mem_iff e₀).mp he₀
  have hleft : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d₀)) =
      X.toCombMap.faceOf d₀ := by
    rw [X.toCombMap.alpha_involutive d₀]
  have hright : X.toCombMap.faceOf (X.toCombMap.alpha y) = X.toCombMap.faceOf e₀ := by
    have hp : X.toCombMap.facePerm (X.toCombMap.alpha y) = e₀ := by
      show X.toCombMap.sigma (X.toCombMap.alpha (X.toCombMap.alpha y)) = e₀
      rw [X.toCombMap.alpha_involutive y]
      exact hy
    rw [← hp, X.toCombMap.faceOf_facePerm]
  have hsame : X.toCombMap.sigma.SameCycle y (X.toCombMap.alpha d₀) :=
    ⟨((k₀ + 1 : ℕ) : ℤ), by rw [zpow_natCast, pow_succ, Perm.mul_apply, hy, hk₀]⟩
  obtain ⟨cyc⟩ := PinchSplit.exists_cycles (M := X.toCombMap) (x := X.toCombMap.alpha d₀)
    (y := y) (by rw [hleft, hright]; exact hface)
  have hout₀ : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d₀)) ≠ X.outerFace := by
    rw [hleft]
    exact fun h => K.outerFace_not_mem (by rw [← h]; exact hf₀)
  have hout₁ : X.toCombMap.faceOf (X.toCombMap.alpha y) ≠ X.outerFace := by
    rw [hright]
    exact fun h => K.outerFace_not_mem (by rw [← h]; exact hf₁)
  have hnc₀ : ∀ C ∈ X.relatorCells,
      C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d₀)) := by
    rw [hleft]
    exact hcell₀
  have hnc₁ : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha y) := by
    rw [hright]
    exact hcell₁
  have hin₀ : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d₀)) ∈ K.faces := by
    rw [hleft]
    exact hf₀
  have hin₁ : X.toCombMap.faceOf (X.toCombMap.alpha y) ∈ K.faces := by
    rw [hright]
    exact hf₁
  exact ⟨⟨X.toCombMap.alpha d₀, y, hsame.symm, cyc, hout₀, hout₁, hnc₀, hnc₁⟩, rfl, hy, hin₀,
    hin₁⟩

/-- **A turn survives the split.** -/
theorem firstTurn_pinchSplitInside [DecidableEq X.toCombMap.Dart]
    (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X) {d₀ e₀ : X.toCombMap.Dart}
    (hd₀ : d₀ ∈ K.boundary.cycle) (he₀ : e₀ ∈ K.boundary.cycle)
    (hx : I.x = X.toCombMap.alpha d₀) (hy : X.toCombMap.sigma I.y = e₀)
    {d e : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) (he : e ∈ K.boundary.cycle)
    (h : FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e) (X.toCombMap.alpha d)) :
    FirstTurn I.diagram.toCombMap (K.boundary.cycle.reverse.map I.diagram.toCombMap.alpha)
      (I.diagram.toCombMap.alpha e) (I.diagram.toCombMap.alpha d) := by
  obtain ⟨k, hk, hk', hkeep⟩ := FirstTurn.reverse_map_alpha_iff.mp h
  have havoid := K.avoids_of_turn I hd₀ he₀ hx hy hd he hk' hkeep
  refine FirstTurn.reverse_map_alpha_iff.mpr ⟨k, hk, ?_, fun t ht htk => ?_⟩
  · exact (CellPinchFirstTurn.mul_swap_pow_apply_of_avoids X.toCombMap.sigma I.x I.y e k
      havoid).trans hk'
  · have heq : (I.diagram.toCombMap.sigma ^ t) e = (X.toCombMap.sigma ^ t) e :=
      CellPinchFirstTurn.mul_swap_pow_apply_of_avoids X.toCombMap.sigma I.x I.y e t
        fun i hi => havoid i (hi.trans htk)
    rw [heq]
    exact hkeep t ht htk

/-- **The split cell pocket is in first-turn order.** -/
theorem firstTurns_pinchSplitInside [DecidableEq X.toCombMap.Dart]
    (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X) (hs : I.Inside K.faces)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) (he₀ : e₀ ∈ K.boundary.cycle)
    (hx : I.x = X.toCombMap.alpha d₀) (hy : X.toCombMap.sigma I.y = e₀) (hK : K.FirstTurns) :
    (K.pinchSplitInside I hs).FirstTurns :=
  ⟨hK.1.imp_of_mem_imp fun _ _ hd he h => K.firstTurn_pinchSplitInside I hd₀ he₀ hx hy hd he h,
    K.firstTurn_pinchSplitInside I hd₀ he₀ hx hy (List.getLast_mem K.boundary.cycle_nonempty)
      (List.head_mem K.boundary.cycle_nonempty) hK.2⟩

/-- **The split at the end of a turn lowers the repeated visits.** -/
theorem pinchSplitInside_repeatedVisits_lt_of_turn [DecidableEq X.toCombMap.Dart]
    (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X) (hs : I.Inside K.faces)
    {d₀ e₀ e : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) (he₀ : e₀ ∈ K.boundary.cycle)
    (hx : I.x = X.toCombMap.alpha d₀) (hy : X.toCombMap.sigma I.y = e₀) {k₀ : ℕ}
    (hk₀ : (X.toCombMap.sigma ^ k₀) e₀ = X.toCombMap.alpha d₀)
    (hkeep₀ : ∀ t, 0 < t → t < k₀ →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀))
    (he : e ∈ K.boundary.cycle) (hne : e ≠ e₀)
    (hv : X.toCombMap.vertexOf e = X.toCombMap.vertexOf e₀) :
    (K.pinchSplitInside I hs).repeatedVisits < K.repeatedVisits := by
  have havoid₀ := K.avoids_of_turn I hd₀ he₀ hx hy hd₀ he₀ hk₀ hkeep₀
  have hy₁ : ∀ i ≤ k₀, (X.toCombMap.sigma ^ i) e₀ ≠ I.y := by
    intro i hi
    rcases Nat.lt_or_ge i k₀ with hlt | hge
    · exact (havoid₀ i hlt).2
    · obtain rfl : i = k₀ := by omega
      rw [hk₀, ← hx]
      exact I.cycles.ne
  have hex : ∃ n : ℕ, (X.toCombMap.sigma ^ n) e = e₀ :=
    ((X.toCombMap.vertexOf_eq_iff e e₀).mp hv).exists_nat_pow_eq
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, (X.toCombMap.sigma ^ n) e = e₀ ∧
      ∀ m < n, (X.toCombMap.sigma ^ m) e ≠ e₀ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    rcases n with _ | n'
    · rw [pow_zero, Perm.one_apply] at hn
      exact absurd hn hne
    · exact ⟨n', rfl⟩
  have hy₂ : (X.toCombMap.sigma ^ n') e = I.y := by
    apply X.toCombMap.sigma.injective
    rw [hy, ← hn, pow_succ', Perm.mul_apply]
  have hx₂ : ∀ i ≤ n', (X.toCombMap.sigma ^ i) e ≠ I.x := by
    intro i hi h
    rw [hx, ← hk₀] at h
    rcases Nat.lt_or_ge i k₀ with hlt | hge
    · obtain ⟨j, rfl⟩ : ∃ j, k₀ = i + j := ⟨k₀ - i, by omega⟩
      rw [pow_add, Perm.mul_apply] at h
      have hj : e = (X.toCombMap.sigma ^ j) e₀ := (X.toCombMap.sigma ^ i).injective h
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [zero_add] at hk₀
        rw [hj, hk₀] at he
        exact K.boundary_alpha_not_mem hd₀ he
      · exact hkeep₀ j (by omega) (by omega) (Or.inl (by rw [← hj]; exact he))
    · obtain ⟨j, rfl⟩ : ∃ j, i = k₀ + j := ⟨i - k₀, by omega⟩
      rw [pow_add, Perm.mul_apply] at h
      exact hmin j (by omega) ((X.toCombMap.sigma ^ k₀).injective h)
  exact K.pinchSplitInside_repeatedVisits_lt I hs he₀ he
    ((I.diagram.toCombMap.vertexOf_eq_iff e₀ I.x).mpr
      (I.sameCycle_x_of_stretch (hk₀.trans hx.symm) hy₁))
    ((I.diagram.toCombMap.vertexOf_eq_iff e I.y).mpr (I.sameCycle_y_of_stretch hy₂ hx₂))

/-! ## The step at good corners -/

/-- **One step of the cell pinch at a turn into a vertex visited twice**, for a cell pocket in
first-turn order on a diagram whose labels are letters, when the darts of the turn lie on distinct
faces other than relator faces. -/
theorem exists_firstTurnStep_of_turn
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.FirstTurns) {d₀ e₀ e : X.toCombMap.Dart}
    (hd₀ : d₀ ∈ K.boundary.cycle) (he₀ : e₀ ∈ K.boundary.cycle) (he : e ∈ K.boundary.cycle)
    (hne : e ≠ e₀) (hv : X.toCombMap.vertexOf e = X.toCombMap.vertexOf e₀)
    (hturn : FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (hface : X.toCombMap.faceOf d₀ ≠ X.toCombMap.faceOf e₀)
    (hcell₀ : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf d₀)
    (hcell₁ : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf e₀) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.FirstTurns ∧ K'.repeatedVisits < K.repeatedVisits := by
  classical
  obtain ⟨k₀, -, hk₀, hkeep₀⟩ := FirstTurn.reverse_map_alpha_iff.mp hturn
  obtain ⟨I, hx, hy, hs⟩ := K.exists_turnInput hd₀ he₀ hk₀ hface hcell₀ hcell₁
  exact ⟨I.diagram, I.cellMap.indexEquiv i, I.cellMap.indexEquiv j, K.pinchSplitInside I hs,
    ⟨I.oEquivalent⟩, I.label_isLetter (symmetricLabelAlphabet D) hlabel,
    K.firstTurns_pinchSplitInside I hs hd₀ he₀ hx hy hK,
    K.pinchSplitInside_repeatedVisits_lt_of_turn I hs hd₀ he₀ hx hy hk₀ hkeep₀ he hne hv⟩

/-- **Good corners**: no dart of the boundary cycle lies on a relator face, and distinct darts of
the cycle lie on distinct faces. -/
def GoodCorners (K : CellPocketFaceSet D eps X i j) : Prop :=
  (∀ d ∈ K.boundary.cycle, ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf d) ∧
    ∀ d ∈ K.boundary.cycle, ∀ e ∈ K.boundary.cycle,
      X.toCombMap.faceOf d = X.toCombMap.faceOf e → d = e

/-- **One step of the cell pinch for a pinched cell pocket in first-turn order with good
corners.** -/
theorem exists_firstTurnStep_of_goodCorners
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.FirstTurns) (hgood : K.GoodCorners)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.FirstTurns ∧ K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨d₀, hd₀, e₀, he₀, e, he, hne₀, hne, hv, hturn⟩ :=
    K.exists_turn_of_not_unpinched hK hpinch
  exact K.exists_firstTurnStep_of_turn hlabel hK hd₀ he₀ he hne hv hturn
    (fun h => hne₀ (hgood.2 d₀ hd₀ e₀ he₀ h)) (hgood.1 d₀ hd₀) (hgood.1 e₀ he₀)

end CellPocketFaceSet

/-- **One step of the cell pinch for a cell pocket in first-turn order with good corners.**  A
pinched cell pocket face set in first-turn order, whose boundary darts lie on distinct faces other
than relator faces, on a diagram whose labels are letters, has an O-equivalent copy whose labels are
letters, with a cell pocket face set in first-turn order and fewer repeated visits. -/
def CellPocketPinchGoodCornerStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.FirstTurns → K.GoodCorners →
      ¬Unpinched X.toCombMap K.faces →
      ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
        (K' : CellPocketFaceSet D eps X' i' j'),
        Nonempty (OEquivalentDiscDiagram X X') ∧
          (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.FirstTurns ∧ K'.repeatedVisits < K.repeatedVisits

theorem cellPocketPinchGoodCornerStep : CellPocketPinchGoodCornerStepStatement.{u, w, v} := by
  intro G _ Lambda D eps W X i j hlabel K hK hgood hpinch
  exact K.exists_firstTurnStep_of_goodCorners hlabel hK hgood hpinch

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.FirstTurns.closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_turn_of_not_unpinched
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_turnInput
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.firstTurns_pinchSplitInside
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplitInside_repeatedVisits_lt_of_turn
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_firstTurnStep_of_goodCorners
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchGoodCornerStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchGoodCornerStep
