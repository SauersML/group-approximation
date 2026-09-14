import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# Sides along the vertex rotation of a noncrossing closed walk

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The vertex count of the two reclosings of a noncrossing closed walk `w` reads the rotation at a vertex
side by side.  One rotation step keeps the face across: `faceOf (sigma y) = faceOf (alpha y)`.  A dart
on an edge off the walk has both of its faces on one side of the walk.  So rotating from a dart based
outside the side of `w`, the darts stay outside until the reversal of a walk dart; the next dart is
based on the side.  Rotating from a dart based on the side, the darts stay there until a walk dart;
the next dart is based outside.  Around a vertex the reversals of walk darts and the walk darts
alternate.

* `IsNoncrossingClosedWalk.faceOf_sigma`: one rotation step keeps the face across.
* `IsNoncrossingClosedWalk.alpha_mem_of_faceOf_sigma_mem`: a step from outside to the side starts at
  the reversal of a walk dart.
* `IsNoncrossingClosedWalk.mem_of_faceOf_sigma_not_mem`: a step from the side to outside starts at a
  walk dart.
* `IsNoncrossingClosedWalk.faceOf_mem_of_mem`, `faceOf_alpha_not_mem_of_mem`: the sides of a walk
  dart and of its reversal.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **One rotation step keeps the face across**: `sigma y` is the face step from `alpha y`. -/
theorem faceOf_sigma (M : CombMap.{u}) (y : M.Dart) : M.faceOf (M.sigma y) = M.faceOf (M.alpha y) := by
  have h : M.facePerm (M.alpha y) = M.sigma y := by
    show M.sigma (M.alpha (M.alpha y)) = M.sigma y
    rw [M.alpha_involutive y]
  rw [← h, M.faceOf_facePerm]

/-- A walk dart is based on the side of the walk. -/
theorem faceOf_mem_of_mem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) {d : M.Dart}
    (hd : d ∈ w) : M.faceOf d ∈ sideFaces M w :=
  ((hw.isBoundaryDart_sideFaces_iff hM d).mpr hd).1

/-- The reversal of a walk dart is based outside the side of the walk. -/
theorem faceOf_alpha_not_mem_of_mem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {d : M.Dart} (hd : d ∈ w) : M.faceOf (M.alpha d) ∉ sideFaces M w :=
  ((hw.isBoundaryDart_sideFaces_iff hM d).mpr hd).2

/-- **A step from outside to the side starts at the reversal of a walk dart.** -/
theorem alpha_mem_of_faceOf_sigma_mem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {y : M.Dart} (hy : M.faceOf y ∉ sideFaces M w) (hs : M.faceOf (M.sigma y) ∈ sideFaces M w) :
    M.alpha y ∈ w := by
  rw [faceOf_sigma M y] at hs
  exact (hw.faceOf_alpha_mem_iff hM (fun hint => hy hint.1)).mp hs

/-- **A step from the side to outside starts at a walk dart.** -/
theorem mem_of_faceOf_sigma_not_mem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {y : M.Dart} (hy : M.faceOf y ∈ sideFaces M w) (hs : M.faceOf (M.sigma y) ∉ sideFaces M w) :
    y ∈ w := by
  rw [faceOf_sigma M y] at hs
  exact (hw.isBoundaryDart_sideFaces_iff hM y).mp ⟨hy, hs⟩

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.faceOf_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.alpha_mem_of_faceOf_sigma_mem
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.mem_of_faceOf_sigma_not_mem

