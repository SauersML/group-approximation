import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkOuterKindClass
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkInnerKindInvariant
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkReclosedVertex
import GroupApproximation.Meta.AxiomGuard

/-!
# The outer classifier by kind is invariant under the outer reclosed rotation

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk whose passages have free sectors, and `x` a retained outer dart.
A retained outer dart has its reversal on the outer side exactly when it is a walk dart, and then the
outer reclosed rotation turns from `w[l+1]` to `alpha w[l]`.
* At an untouched vertex or a vertex with an adjacent passage the class is the vertex, and the outer
  reclosed rotation keeps the vertex (`IsNoncrossingClosedWalk.vertexOf_outerSigma`).
* At a touched vertex without adjacent passage, if `x` is not a walk dart, the reclosed rotation is old
  rotation, and the first walk dart met is met one step later.
* If `x = w[l+1]`, the reclosed rotation turns to `alpha w[l]`, and the short free sector of the passage
  at `l` meets `w[l+1]` first.

* `IsNoncrossingClosedWalk.faceOf_alpha_mem_sideOutside_iff`, `prev_get_finRotate`.
* `IsNoncrossingClosedWalk.outerSigma_pow_not_internal`, `outerSigma_pow_val`: before rotation meets a
  walk dart, outer reclosed rotation is old rotation.
* `IsNoncrossingClosedWalk.outerKindClass_sigma`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides SectorNoninterleaving NoncrossingClosedWalkEuler

universe u

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

private theorem faceOf_sigma_alpha' (M : CombMap.{u}) (d : M.Dart) :
    M.faceOf (M.sigma d) = M.faceOf (M.alpha d) := by
  have h : M.facePerm (M.alpha d) = M.sigma d := by
    change M.sigma (M.alpha (M.alpha d)) = M.sigma d
    rw [M.alpha_involutive d]
  rw [← h, M.faceOf_facePerm]

/-- **A retained outer dart has its reversal on the outer side exactly when it is a walk dart.** -/
theorem faceOf_alpha_mem_sideOutside_iff (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {x : M.Dart} (hx : ¬InternalDart M (sideOutside M w) x) :
    M.faceOf (M.alpha x) ∈ sideOutside M w ↔ x ∈ w := by
  have h := hw.isBoundaryDart_sideOutside_iff hM (M.alpha x)
  rw [M.alpha_involutive x] at h
  rw [← h]
  constructor
  · intro hmem
    refine ⟨hmem, ?_⟩
    rw [M.alpha_involutive x]
    exact fun hx' => hx ⟨hx', hmem⟩
  · exact fun hb => hb.1

/-- **The predecessor of the walk dart at the next position.** -/
theorem prev_get_finRotate [DecidableEq M.Dart] (hnodup : w.Nodup) (l : Fin w.length)
    (h : w.get (finRotate w.length l) ∈ w) :
    w.prev (w.get (finRotate w.length l)) h = w.get l := by
  have key : ∀ (d : M.Dart) (hd : d ∈ w), d = w.next (w.get l) (List.get_mem w l) →
      w.prev d hd = w.get l := by
    rintro d hd rfl
    exact List.prev_next w hnodup _ _
  exact key _ h (next_get_eq hnodup l).symm

/-- **Old rotation from a retained outer dart stays retained until it meets a walk dart.** -/
theorem outerSigma_pow_not_internal (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideOutside M w)) (m : ℕ) (hmin : ∀ j < m, (M.sigma ^ j) x.1 ∉ w) :
    ¬InternalDart M (sideOutside M w) ((M.sigma ^ m) x.1) := by
  induction m with
  | zero =>
    rw [pow_zero, Perm.one_apply]
    exact x.2
  | succ m ih =>
    have hy := ih fun j hj => hmin j (by omega)
    have hface : M.faceOf (M.alpha ((M.sigma ^ m) x.1)) ∉ sideOutside M w := fun h =>
      hmin m (by omega) ((hw.faceOf_alpha_mem_sideOutside_iff hM hy).mp h)
    intro hint
    have h1 := hint.1
    rw [pow_succ', Perm.mul_apply, faceOf_sigma_alpha' M] at h1
    exact hface h1

/-- **Before rotation meets a walk dart, outer reclosed rotation is old rotation.** -/
theorem outerSigma_pow_val (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x : KeptDart M (sideOutside M w)) (m : ℕ) (hmin : ∀ j < m, (M.sigma ^ j) x.1 ∉ w) :
    (((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma ^ m) x).1 =
      (M.sigma ^ m) x.1 := by
  induction m with
  | zero => simp only [pow_zero, Perm.one_apply]
  | succ m ih =>
    have ih' := ih fun j hj => hmin j (by omega)
    have hface : M.faceOf (M.alpha
        (((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma ^ m) x).1) ∉
          sideOutside M w := by
      rw [ih']
      exact fun h => hmin m (by omega) ((hw.faceOf_alpha_mem_sideOutside_iff hM
        (hw.outerSigma_pow_not_internal hM x m fun j hj => hmin j (by omega))).mp h)
    rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply,
      reclosed_sigma_val_of_notMem (hw.outerCycle hM) _ hface, ih']

/-- **The outer classifier by kind is invariant under the outer reclosed rotation.** -/
theorem outerKindClass_sigma (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (x : KeptDart M (sideOutside M w)) :
    hw.outerKindClass ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x) =
      hw.outerKindClass x := by
  classical
  have hv : M.vertexOf ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x).1 =
      M.vertexOf x.1 := hw.vertexOf_outerSigma hM x
  by_cases hS : Touched M w (M.vertexOf x.1) ∧ ¬ AdjVertex M w (M.vertexOf x.1)
  · have hSy : Touched M w
          (M.vertexOf ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x).1) ∧
        ¬ AdjVertex M w
          (M.vertexOf ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x).1) := by
      rw [hv]; exact hS
    by_cases hxw : x.1 ∈ w
    · obtain ⟨p, hp⟩ := List.get_of_mem hxw
      obtain ⟨l, hxl⟩ : ∃ l : Fin w.length, x.1 = w.get (finRotate w.length l) :=
        ⟨(finRotate w.length).symm p, by rw [Equiv.apply_symm_apply, hp]⟩
      have hnadj : ¬ PassageAdjacent M w l := fun hadj => hS.2
        ⟨l, by rw [get_finRotate_of_isChain_closes hw.ne_nil hw.chain hw.closes, ← hxl], hadj⟩
      have hcx := hw.outerKindClass_eq_inr x hS hnadj (m := 0)
        (by rw [pow_zero, Perm.one_apply]; exact hxl) (fun j hj => absurd hj (Nat.not_lt_zero j))
      have hx : M.faceOf (M.alpha x.1) ∈ sideOutside M w :=
        (hw.faceOf_alpha_mem_sideOutside_iff hM x.2).mpr hxw
      have key : ∀ (d : M.Dart) (hd : d ∈ w), d = w.get (finRotate w.length l) →
          M.alpha (w.prev d hd) = M.alpha (w.get l) := by
        rintro d hd rfl
        rw [prev_get_finRotate hw.nodup l hd]
      have hyv : ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x).1 =
          M.alpha (w.get l) := by
        rw [reclosed_sigma_val_of_mem (hw.outerCycle hM) x hx, hw.outerCycle_boundaryPerm_val hM]
        exact key _ _ (by
          show M.alpha (M.alpha x.1) = w.get (finRotate w.length l)
          rw [M.alpha_involutive]; exact hxl)
      obtain ⟨a, ha, hafree⟩ := (hsector l).resolve_right hnadj
      have hcy := hw.outerKindClass_eq_inr
        ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x) hSy hnadj (m := a)
        (by rw [hyv]; exact ha) (fun j hj => by
          rw [hyv]
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · rw [h0, pow_zero, Perm.one_apply]
            exact hw.alpha_not_mem _ (List.get_mem w _)
          · exact fun hmem => hafree j h0 hj (Or.inl hmem))
      exact hcy.trans hcx.symm
    · have hyv : ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x).1 = M.sigma x.1 :=
        reclosed_sigma_val_of_notMem (hw.outerCycle hM) x
          (fun h => hxw ((hw.faceOf_alpha_mem_sideOutside_iff hM x.2).mp h))
      obtain ⟨l, hl, m, hml, hmin⟩ := hw.exists_first_short hS.1 hS.2
      have hcx := hw.outerKindClass_eq_inr x hS hl hml hmin
      rcases m with _ | m
      · rw [pow_zero, Perm.one_apply] at hml
        exact absurd (by rw [hml]; exact List.get_mem w _) hxw
      · have hcy := hw.outerKindClass_eq_inr
          ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x) hSy hl (m := m)
          (by
            have hshift : (M.sigma ^ m) (M.sigma x.1) = (M.sigma ^ (m + 1)) x.1 := by
              rw [pow_succ, Perm.mul_apply]
            rw [hyv, hshift]; exact hml)
          (fun j hj => by
            have hshift : (M.sigma ^ j) (M.sigma x.1) = (M.sigma ^ (j + 1)) x.1 := by
              rw [pow_succ, Perm.mul_apply]
            rw [hyv, hshift]
            exact hmin (j + 1) (by omega))
        exact hcy.trans hcx.symm
  · have hSy : ¬ (Touched M w
          (M.vertexOf ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x).1) ∧
        ¬ AdjVertex M w
          (M.vertexOf ((reclosedMap M (sideOutside M w) (hw.outerCycle hM)).sigma x).1)) := by
      rw [hv]; exact hS
    rw [hw.outerKindClass_eq_inl _ hSy, hw.outerKindClass_eq_inl x hS]
    exact congrArg Sum.inl (Subtype.ext hv)

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.faceOf_alpha_mem_sideOutside_iff
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.prev_get_finRotate
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerSigma_pow_val
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.outerKindClass_sigma
