import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops.FaceOrbit
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellBlocks
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellSides
import GroupApproximation.Meta.AxiomGuard

/-!
# End loops of the class producer: pockets

A pocket of cell `i` is a value-one face walk `seg x ℓ` on the cell, `ℓ ≤ n`, whose two ends
`x` and `f^ℓ x` sit at one vertex.  This module proves that pockets concatenate, are at most
`⌈c / λ⌉₊` long, that a longest pocket through a dart exists, that the same-cell pocket value
input produces pockets, and case 1 of the route in `FaceOrbit.lean` (the reverse of the dart
after the longest pocket lies on the cell itself).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

theorem pow_succ_apply {M : CombMap.{v}} (x : M.Dart) (a : ℕ) :
    (M.facePerm ^ (a + 1)) x = M.facePerm ((M.facePerm ^ a) x) := by
  rw [pow_succ', Equiv.Perm.mul_apply]

section Pockets

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

theorem listVal_dartWord_append (X : DiscDiagram.{u, w, v} W) (l₁ l₂ : List X.toCombMap.Dart) :
    RelLetter.listVal (dartWord X (l₁ ++ l₂)) =
      RelLetter.listVal (dartWord X l₁) * RelLetter.listVal (dartWord X l₂) := by
  rw [dartWord_append, HullSC.RelWord.listVal_append]

theorem exists_outer (X : DiscDiagram.{u, w, v} W) :
    ∃ o : X.toCombMap.Dart, X.toCombMap.faceOf o = X.outerFace := by
  obtain ⟨o, ho⟩ := Quotient.exists_rep X.outerFace
  exact ⟨o, ho⟩

/-- A pocket of cell `i`: a value-one face walk on the cell with both ends at one vertex. -/
def IsPocket (X : DiscDiagram.{u, w, v} W) (i : Fin X.rCellCount) (x : X.toCombMap.Dart)
    (l : ℕ) : Prop :=
  x ∈ cellDarts X i ∧ l ≤ (cellDarts X i).length ∧
    X.toCombMap.sigma.SameCycle x ((X.toCombMap.facePerm ^ l) x) ∧
    RelLetter.listVal (dartWord X (seg X.toCombMap x l)) = 1

/-- A pocket of length `l` containing the dart `d`. -/
def PocketThrough (X : DiscDiagram.{u, w, v} W) (i : Fin X.rCellCount) (d : X.toCombMap.Dart)
    (l : ℕ) : Prop :=
  ∃ (x : X.toCombMap.Dart) (t : ℕ), t < l ∧ (X.toCombMap.facePerm ^ t) x = d ∧ IsPocket X i x l

variable {X : DiscDiagram.{u, w, v} W} {i : Fin X.rCellCount}

/-- Two consecutive pockets form a pocket. -/
theorem IsPocket.append {x : X.toCombMap.Dart} {a b : ℕ} (ha : IsPocket X i x a)
    (hb : IsPocket X i ((X.toCombMap.facePerm ^ a) x) b)
    (hab : a + b ≤ (cellDarts X i).length) : IsPocket X i x (a + b) := by
  refine ⟨ha.1, hab, ?_, ?_⟩
  · have h := hb.2.2.1
    rw [← pow_apply_add, add_comm b a] at h
    exact ha.2.2.1.trans h
  · rw [seg_add, listVal_dartWord_append, ha.2.2.2, hb.2.2.2, mul_one]

theorem IsPocket.le_ceil {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    {x : X.toCombMap.Dart} {l : ℕ} (h : IsPocket X i x l) : l ≤ ⌈c / lambda⌉₊ :=
  pocket_len_le hW hlambda h.1 h.2.1 h.2.2.2

/-- A longest pocket through a dart. -/
theorem exists_max_pocket {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    {d : X.toCombMap.Dart} {l : ℕ} (h : PocketThrough X i d l) :
    ∃ J, PocketThrough X i d J ∧ ∀ l', PocketThrough X i d l' → l' ≤ J := by
  have hl : l ≤ ⌈c / lambda⌉₊ := by
    obtain ⟨_, _, -, -, hx⟩ := h
    exact hx.le_ceil hW hlambda
  refine ⟨Nat.findGreatest (PocketThrough X i d) ⌈c / lambda⌉₊,
    Nat.findGreatest_spec (P := PocketThrough X i d) hl h,
    fun l' hl' => Nat.le_findGreatest (P := PocketThrough X i d) ?_ hl'⟩
  obtain ⟨_, _, -, -, hx⟩ := hl'
  exact hx.le_ceil hW hlambda

/-- The same-cell pocket value input gives a pocket from an oriented same-cell dart. -/
theorem pocket_of_value (hpv : OsinUnboundSameCellBlocks.PocketValue X)
    {z : X.toCombMap.Dart} (hz : z ∈ cellDarts X i)
    (hface : X.toCombMap.faceOf (X.toCombMap.alpha z) = (cell X i).face)
    (hor : ∃ o : X.toCombMap.Dart, X.toCombMap.faceOf o = X.outerFace ∧
      Relation.EqvGen (AvoidEdgeStep X.toCombMap z) z o)
    {m : ℕ} (hm : m + 1 < (cellDarts X i).length)
    (hstep : (X.toCombMap.facePerm ^ (m + 1)) z = X.toCombMap.alpha z) :
    IsPocket X i z (m + 2) := by
  have hval := hpv i z hz hface hor m hm hstep
  refine ⟨hz, by omega, ?_, ?_⟩
  · rw [show m + 2 = m + 1 + 1 from rfl, pow_succ_apply, hstep]
    show X.toCombMap.sigma.SameCycle z
      (X.toCombMap.sigma (X.toCombMap.alpha (X.toCombMap.alpha z)))
    rw [X.toCombMap.alpha_involutive z]
    exact (Equiv.Perm.SameCycle.refl _ _).apply_right
  · have hmap : seg X.toCombMap (X.toCombMap.facePerm z) m =
        (List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) z := by
      simp only [seg]
      apply List.map_congr_left
      intro t _
      simp only [pow_succ, Equiv.Perm.mul_apply]
    rw [show m + 2 = m + 1 + 1 from rfl, seg_succ, hstep, seg_succ', hmap]
    show RelLetter.listVal (dartWord X (([z] ++
      (List.range m).map fun t => (X.toCombMap.facePerm ^ (t + 1)) z) ++
        [X.toCombMap.alpha z])) = 1
    rw [listVal_dartWord_append, listVal_dartWord_append, hval, mul_one,
      ← listVal_dartWord_append]
    exact (listVal_dartWord_erase_alpha_pair X [] [] z).trans RelLetter.listVal_nil

/-- **Case 1.**  After a longest pocket `seg x J` through `d`, the reverse of `p = f^J x` does
not lie on the cell. -/
theorem case_same_face (hpv : OsinUnboundSameCellBlocks.PocketValue X)
    {x d : X.toCombMap.Dart} {J s : ℕ} (hx : IsPocket X i x J) (hs : s < J)
    (hd : (X.toCombMap.facePerm ^ s) x = d)
    (hmax : ∀ l', PocketThrough X i d l' → l' ≤ J)
    (hsep : ∀ j < J, (X.toCombMap.facePerm ^ j) x ≠
      X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x))
    (hface : X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x)) =
      (cell X i).face) : False := by
  obtain ⟨q, hq, hqp⟩ := exists_pow_cell hx.1 (mem_cell_of_faceOf hface)
  have hp : (X.toCombMap.facePerm ^ J) x ∈ cellDarts X i := pow_mem_cell hx.1 J
  rcases lt_trichotomy q J with hlt | heq | hgt
  · exact hsep q hlt hqp
  · rw [heq] at hqp
    exact X.toCombMap.alpha_fixedPointFree _ hqp.symm
  · have hpface : X.toCombMap.faceOf (X.toCombMap.alpha
        (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x))) = (cell X i).face := by
      rw [X.toCombMap.alpha_involutive ((X.toCombMap.facePerm ^ J) x)]
      exact faceOf_of_mem_cellDarts hp
    rcases AvoidEdgeStep.oriented_or X.planar.1 (exists_outer X)
        ((X.toCombMap.facePerm ^ J) x) with hor | hor
    · have hstep : (X.toCombMap.facePerm ^ (q - J - 1 + 1)) ((X.toCombMap.facePerm ^ J) x) =
          X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x) := by
        rw [← pow_apply_add, show q - J - 1 + 1 + J = q by omega, hqp]
      have hP := pocket_of_value hpv hp hface hor (by omega) hstep
      have hlong := hmax (J + (q - J - 1 + 2)) ⟨x, s, by omega, hd, hx.append hP (by omega)⟩
      omega
    · have hstep : (X.toCombMap.facePerm ^ ((cellDarts X i).length - q + J - 1 + 1))
            (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x)) =
          X.toCombMap.alpha (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x)) := by
        rw [X.toCombMap.alpha_involutive ((X.toCombMap.facePerm ^ J) x), ← hqp, ← pow_apply_add,
          show (cellDarts X i).length - q + J - 1 + 1 + q = J + (cellDarts X i).length by omega,
          pow_add_length_cell hx.1]
      have hP := pocket_of_value hpv (mem_cell_of_faceOf hface) hpface hor (by omega) hstep
      have hd' : (X.toCombMap.facePerm ^ ((cellDarts X i).length - q + s))
          (X.toCombMap.alpha ((X.toCombMap.facePerm ^ J) x)) = d := by
        rw [← hqp, ← pow_apply_add,
          show (cellDarts X i).length - q + s + q = s + (cellDarts X i).length by omega,
          pow_add_length_cell hx.1, hd]
      have hlong := hmax ((cellDarts X i).length - q + J - 1 + 2) ⟨_, _, by omega, hd', hP⟩
      omega

end Pockets

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ClassJoinsEndLoops
