import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Chord
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the step at an uncrossed non-first turn with a good sector

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Step 4 of the plan in `Piece06/Predicate`.

Let `d₀ → e₀` be an uncrossed non-first turn of the boundary cycle `c` of a cell pocket `K` in walk
order.

* The rotation from `e₀` to `x = σ^m e₀` meets no edge of `c` (`hkeepm`); then every corner
  `face (α (σ^t e₀))`, `t ≤ m`, lies off `K.faces` (`faceOf_alpha_sectorAfter_not_mem`), by induction:
  `face (α e₀)` is off `K.faces` since `e₀` is a boundary dart, and if `face (α u)` is off `K.faces`
  then so is `face (σ u) = face (facePerm (α u))`, so `face (α (σ u))` in `K.faces` would make
  `α (σ u)` a boundary dart, an edge of `c`.
* Symmetrically, the rotation from `y` to `σ^q y = α d₀` meets no edge of `c` (`hkeepq`); then every
  face `face (σ^(q - n) y)`, `n < q`, lies off `K.faces` (`faceOf_sectorBefore_not_mem`), and in
  particular `face (α y) = face (σ y)` does (`faceOf_alpha_before_not_mem`).
* When the two corner faces are distinct, off the exterior and off the relator cells, they form a
  `PinchSplit.Input` (`exists_input`), and it avoids `K.faces`.  The turn is uncrossed, so
  `Piece06.exists_step_of_uncrossedTurn` gives the step, with the first arrival `k₀` of `e₀` from
  `α d₀` (`OuterPinchCorners.exists_firstArrival`) and the dart `z₀` outside the sector
  (`OuterPinchCorners.exists_outside_of_not_firstTurn`).  This is `exists_step_of_goodSector`.
* The minimal sector `m = 0`, `q = 1`, `x = e₀`, `y = σ⁻¹ (α d₀)`, whose corner faces are `face (α e₀)`
  and `face (α (σ⁻¹ (α d₀))) = face (α d₀)` (`faceOf_alpha_sigma_symm`): `exists_step_of_goodCorners`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated OuterPinchCorners
  OuterPinchCornerFix
open scoped Classical

/-- The corner before `alpha d` lies on the face of `alpha d`: `face (α (σ⁻¹ z)) = face z`. -/
theorem faceOf_alpha_sigma_symm (M : CombMap.{v}) (z : M.Dart) :
    M.faceOf (M.alpha (M.sigma.symm z)) = M.faceOf z := by
  rw [← M.faceOf_facePerm (M.alpha (M.sigma.symm z)), facePerm_alpha, Equiv.apply_symm_apply]

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A split input from good corners.** -/
theorem exists_input {x y : X.toCombMap.Dart} (hsame : X.toCombMap.sigma.SameCycle x y)
    (hne : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.toCombMap.faceOf (X.toCombMap.alpha y))
    (hxout : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.outerFace)
    (hyout : X.toCombMap.faceOf (X.toCombMap.alpha y) ≠ X.outerFace)
    (hxcell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha x))
    (hycell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha y)) :
    ∃ I : PinchSplit.Input X, I.x = x ∧ I.y = y :=
  ⟨⟨x, y, hsame, (PinchSplit.exists_cycles hne).some, hxout, hyout, hxcell, hycell⟩, rfl, rfl⟩

/-- **The corners after `e₀` lie off the face set**, up to the first edge of the cycle. -/
theorem faceOf_alpha_sectorAfter_not_mem (K : CellPocketFaceSet D eps X i j)
    {e₀ : X.toCombMap.Dart} (he₀ : e₀ ∈ K.boundary.cycle) {m : ℕ}
    (hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀)) :
    ∀ t, t ≤ m →
      X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.sigma ^ t) e₀)) ∉ K.faces := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [pow_zero, Equiv.Perm.one_apply]
    exact ((K.boundary.cycle_mem_iff e₀).mp he₀).2
  | succ t ih =>
    intro ht hmem
    have hprev : X.toCombMap.faceOf ((X.toCombMap.sigma ^ (t + 1)) e₀) ∉ K.faces := by
      rw [pow_succ', Equiv.Perm.mul_apply, ← facePerm_alpha ((X.toCombMap.sigma ^ t) e₀),
        X.toCombMap.faceOf_facePerm]
      exact ih (Nat.le_of_succ_le ht)
    refine hkeepm (t + 1) (Nat.succ_pos t) ht (Or.inr ?_)
    refine (K.boundary.cycle_mem_iff _).mpr ⟨hmem, ?_⟩
    rw [X.toCombMap.alpha_involutive]
    exact hprev

/-- **The faces before `alpha d₀` lie off the face set**, back to the last edge of the cycle. -/
theorem faceOf_sectorBefore_not_mem (K : CellPocketFaceSet D eps X i j)
    {d₀ y : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) {q : ℕ}
    (hq : (X.toCombMap.sigma ^ q) y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) y)) :
    ∀ n, n < q → X.toCombMap.faceOf ((X.toCombMap.sigma ^ (q - n)) y) ∉ K.faces := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.sub_zero, hq]
    exact ((K.boundary.cycle_mem_iff d₀).mp hd₀).2
  | succ n ih =>
    intro hn hmem
    have hs : q - n = q - (n + 1) + 1 := by omega
    have h := ih (Nat.lt_of_succ_lt hn)
    rw [hs, pow_succ', Equiv.Perm.mul_apply,
      ← facePerm_alpha ((X.toCombMap.sigma ^ (q - (n + 1))) y), X.toCombMap.faceOf_facePerm] at h
    refine hkeepq (q - (n + 1)) (by omega) (by omega) (Or.inl ?_)
    exact (K.boundary.cycle_mem_iff _).mpr ⟨hmem, h⟩

/-- **The corner at `y` lies off the face set.** -/
theorem faceOf_alpha_before_not_mem (K : CellPocketFaceSet D eps X i j)
    {d₀ y : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) {q : ℕ}
    (hq : (X.toCombMap.sigma ^ q) y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) y)) (hq0 : 0 < q) :
    X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ K.faces := by
  have h := faceOf_sectorBefore_not_mem K hd₀ hq hkeepq (q - 1) (by omega)
  rw [show q - (q - 1) = 1 by omega, pow_one, ← facePerm_alpha y, X.toCombMap.faceOf_facePerm] at h
  exact h

/-- **One step of the cell pinch at an uncrossed non-first turn with a good sector, for distinct
cells.** -/
theorem exists_step_of_goodSector
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    {x y : X.toCombMap.Dart} {m q : ℕ} (hm : (X.toCombMap.sigma ^ m) e₀ = x)
    (hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀))
    (hq0 : 0 < q) (hq : (X.toCombMap.sigma ^ q) y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) y))
    (hne : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.toCombMap.faceOf (X.toCombMap.alpha y))
    (hxout : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.outerFace)
    (hyout : X.toCombMap.faceOf (X.toCombMap.alpha y) ≠ X.outerFace)
    (hxcell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha x))
    (hycell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha y)) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  have hc : ∀ d ∈ K.boundary.cycle, X.toCombMap.alpha d ∉ K.boundary.cycle :=
    fun d hd => K.boundary_alpha_not_mem hd
  have he₀ : e₀ ∈ K.boundary.cycle := by
    rw [← hnext₀]
    exact List.next_mem ..
  have hαe : X.toCombMap.alpha d₀ ≠ e₀ := fun h => hc d₀ hd₀ (by rw [h]; exact he₀)
  have hvert : X.toCombMap.vertexOf (X.toCombMap.alpha d₀) = X.toCombMap.vertexOf e₀ := by
    have h := rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup hK.1 hK.2 hd₀
    rwa [hnext₀] at h
  have hsame : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) e₀ :=
    (X.toCombMap.vertexOf_eq_iff _ _).mp hvert
  obtain ⟨k₀, -, hk₀, hk₀min⟩ := exists_firstArrival hsame hαe
  obtain ⟨z₀, hz₀, hz₀v, hz₀e, hz₀out⟩ := exists_outside_of_not_firstTurn K.boundary.cycle_nonempty
    K.boundary.cycle_nodup hc hK.1 hK.2 hd₀ hnext₀ huncross hk₀ hk₀min hnot
  have hxy : X.toCombMap.sigma.SameCycle x y :=
    (sameCycle_of_pow_eq hm).symm.trans (hsame.symm.trans (sameCycle_of_pow_eq hq).symm)
  have hxs : X.toCombMap.faceOf (X.toCombMap.alpha x) ∉ K.faces := by
    have h := faceOf_alpha_sectorAfter_not_mem K he₀ hkeepm m le_rfl
    rwa [hm] at h
  have hys := faceOf_alpha_before_not_mem K hd₀ hq hkeepq hq0
  obtain ⟨I, hx, hy⟩ := exists_input hxy hne hxout hyout hxcell hycell
  subst hx hy
  exact exists_step_of_uncrossedTurn hlabel K hK hij hfirst hsecond I ⟨hxs, hys⟩ hd₀ hnext₀
    huncross hk₀ hk₀min hm hkeepm hq0 hq hkeepq hz₀ hz₀v hz₀e hz₀out

/-- **One step of the cell pinch at an uncrossed non-first turn with good corners, for distinct
cells**: the minimal sector `x = e₀`, `y = σ⁻¹ (alpha d₀)`. -/
theorem exists_step_of_goodCorners
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    (hgood : GoodTurnCorners X d₀ e₀) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨hne, hxout, hyout, hxcell, hycell⟩ := hgood
  have hface := faceOf_alpha_sigma_symm X.toCombMap (X.toCombMap.alpha d₀)
  exact exists_step_of_goodSector hlabel K hK hij hfirst hsecond hd₀ hnext₀ hnot huncross
    (x := e₀) (y := X.toCombMap.sigma.symm (X.toCombMap.alpha d₀)) (m := 0) (q := 1)
    (by rw [pow_zero, Equiv.Perm.one_apply])
    (fun _ ht0 ht => absurd (Nat.lt_of_lt_of_le ht0 ht) (Nat.lt_irrefl 0))
    Nat.one_pos (by rw [pow_one, Equiv.apply_symm_apply])
    (fun _ ht0 ht1 => absurd (Nat.lt_of_lt_of_le ht0 (Nat.le_of_lt_succ ht1)) (Nat.lt_irrefl 0))
    (by rw [hface]; exact hne) hxout (by rw [hface]; exact hyout) hxcell
    (fun C hC => by rw [hface]; exact hycell C hC)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.faceOf_alpha_sigma_symm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_input
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.faceOf_alpha_sectorAfter_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.faceOf_sectorBefore_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.faceOf_alpha_before_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_goodSector
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_goodCorners
