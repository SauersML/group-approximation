import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkInnerKindClass
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkReclosedVertex
import GroupApproximation.Meta.AxiomGuard

/-!
# The inner classifier by kind is invariant under the inner reclosed rotation

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk whose passages have free sectors, and `x` a retained inner dart.
* At a vertex without adjacent passage the class is the vertex, and the inner reclosed rotation keeps
  the vertex (`IsNoncrossingClosedWalk.vertexOf_innerSigma`).
* At a vertex with an adjacent passage, if `alpha x` is not a walk dart, the reclosed rotation is old
  rotation, and the first reversal met is met one step later.
* If `x = alpha w[l]`, the reclosed rotation turns to `w[l+1]`, and the free stretch of the adjacent
  passage at `l` meets `alpha w[l]` first.

* `IsNoncrossingClosedWalk.next_get_eq`: the successor of the walk dart at a position.
* `IsNoncrossingClosedWalk.innerKindClass_sigma`.

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

private theorem finRotate_val_eq_mod' : ∀ {n : ℕ} (i : Fin n),
    (finRotate n i : ℕ) = (i.val + 1) % n
  | 0, i => i.elim0
  | n + 1, i => by
    rw [coe_finRotate]
    split_ifs with h
    · simp [h]
    · exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ (Fin.val_lt_last h))).symm

/-- **The successor of the walk dart at a position is the dart at the next position.** -/
theorem next_get_eq [DecidableEq M.Dart] (hnodup : w.Nodup) (l : Fin w.length) :
    w.next (w.get l) (List.get_mem w l) = w.get (finRotate w.length l) := by
  have h := List.next_getElem w hnodup l.val l.isLt
  simp only [List.get_eq_getElem]
  rw [h]
  congr 1
  exact (finRotate_val_eq_mod' l).symm

/-- **The inner classifier by kind is invariant under the inner reclosed rotation.** -/
theorem innerKindClass_sigma (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length, PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    (x : KeptDart M (sideFaces M w)) :
    hw.innerKindClass hM hsector ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) =
      hw.innerKindClass hM hsector x := by
  classical
  have hv : M.vertexOf ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1 =
      M.vertexOf x.1 := hw.vertexOf_innerSigma hM x
  by_cases hA : AdjVertex M w (M.vertexOf x.1)
  · have hAy : AdjVertex M w
        (M.vertexOf ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1) := by
      rw [hv]; exact hA
    by_cases ha : M.alpha x.1 ∈ w
    · obtain ⟨l, hl⟩ := List.get_of_mem ha
      have hxl : x.1 = M.alpha (w.get l) := by rw [hl, M.alpha_involutive]
      obtain ⟨i, hi, hadji⟩ := hA
      have hadj : PassageAdjacent M w l :=
        hw.passageAdjacent_of_vertex hM hsector hadji ((congrArg M.vertexOf hxl).symm.trans hi.symm)
      have hcx := hw.innerKindClass_eq_inr hM hsector x ⟨i, hi, hadji⟩ hadj (m := 0)
        (by rw [pow_zero, Perm.one_apply]; exact hxl) (fun j hj => absurd hj (Nat.not_lt_zero j))
      have hx : M.faceOf (M.alpha x.1) ∈ sideFaces M w := (hw.faceOf_alpha_mem_iff hM x.2).mpr ha
      have key : ∀ (d : M.Dart) (hd : d ∈ w), d = w.get l →
          w.next d hd = w.get (finRotate w.length l) := by
        rintro d hd rfl
        exact next_get_eq hw.nodup l
      have hyv : ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1 =
          w.get (finRotate w.length l) := by
        rw [reclosed_sigma_val_of_mem (hw.innerCycle hM) x hx, hw.innerCycle_boundaryPerm_val hM]
        exact key _ _ hl.symm
      obtain ⟨b, hb, hbfree⟩ := id hadj
      have hcy := hw.innerKindClass_eq_inr hM hsector
        ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) hAy hadj (m := b)
        (by rw [hyv]; exact hb) (fun j hj => by
          rw [hyv]
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · rw [h0, pow_zero, Perm.one_apply]
            exact hw.alpha_not_mem _ (List.get_mem w _)
          · exact fun hmem => hbfree j h0 hj (Or.inr hmem))
      exact hcy.trans hcx.symm
    · have hyv : ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1 = M.sigma x.1 :=
        reclosed_sigma_val_of_notMem (hw.innerCycle hM) x
          (fun h => ha ((hw.faceOf_alpha_mem_iff hM x.2).mp h))
      obtain ⟨l, hadj, m, hml, hmin⟩ := hw.exists_first_adjacent hM hsector hA
      have hcx := hw.innerKindClass_eq_inr hM hsector x hA hadj hml hmin
      rcases m with _ | m
      · rw [pow_zero, Perm.one_apply] at hml
        exact absurd (by rw [hml, M.alpha_involutive]; exact List.get_mem w l) ha
      · have hcy := hw.innerKindClass_eq_inr hM hsector
          ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x) hAy hadj (m := m)
          (by rw [hyv, ← Perm.mul_apply, ← pow_succ]; exact hml)
          (fun j hj => by
            have hshift : (M.sigma ^ j) (M.sigma x.1) = (M.sigma ^ (j + 1)) x.1 := by
              rw [pow_succ, Perm.mul_apply]
            rw [hyv, hshift]
            exact hmin (j + 1) (by omega))
        exact hcy.trans hcx.symm
  · have hAy : ¬ AdjVertex M w
        (M.vertexOf ((reclosedMap M (sideFaces M w) (hw.innerCycle hM)).sigma x).1) := by
      rw [hv]; exact hA
    rw [hw.innerKindClass_eq_inl hM hsector _ hAy, hw.innerKindClass_eq_inl hM hsector x hA]
    exact congrArg Sum.inl (Subtype.ext hv)

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.next_get_eq
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.innerKindClass_sigma
