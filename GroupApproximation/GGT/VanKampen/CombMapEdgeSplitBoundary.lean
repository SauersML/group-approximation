import GroupApproximation.GGT.VanKampen.CombMapEdgeSteps
import GroupApproximation.GGT.VanKampen.CombMapEdgeKeptBoundary
import GroupApproximation.GGT.VanKampen.CyclicFaceBoundary

/-!
# The two actual cyclic boundaries obtained by splitting a face

At a chosen boundary index `k`, the inserted negative dart closes the prefix
and the positive dart closes the suffix. Index zero is allowed: its prefix
face is a monogon. Both cyclic lists are constructed with their exact order.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

universe u
variable (M : CombMap.{u}) {f : M.Face} (B : FaceBoundary M f)

def firstCorner : M.Dart := B.darts.get ⟨0, List.length_pos_iff.mpr B.nonempty⟩
def secondCorner (k : Fin B.darts.length) : M.Dart := B.darts.get k

noncomputable abbrev splitMap (k : Fin B.darts.length) : CombMap.{u} :=
  toCombMap M (firstCorner M B) (secondCorner M B k)

def prefixDarts (k : Fin B.darts.length) : List (Dart M) :=
  none :: (B.darts.take k.val).map (embed M)

def suffixDarts (k : Fin B.darts.length) : List (Dart M) :=
  some none :: (B.darts.drop k.val).map (embed M)

theorem corners_face_eq (k : Fin B.darts.length) :
    M.faceOf (firstCorner M B) = M.faceOf (secondCorner M B k) :=
  ((B.mem_iff _).mp (List.get_mem _ _)).trans
    ((B.mem_iff _).mp (List.get_mem _ _)).symm

theorem corner_get_ne (i j : Fin B.darts.length) (hij : i.val ≠ j.val) :
    B.darts.get i ≠ B.darts.get j := by
  intro h
  exact hij (congrArg Fin.val (B.nodup.get_inj_iff.mp h))

theorem corners_ne (k : Fin B.darts.length) (hk : 0 < k.val) :
    firstCorner M B ≠ secondCorner M B k := by
  apply corner_get_ne M B ⟨0, List.length_pos_iff.mpr B.nonempty⟩ k
  change 0 ≠ k.val
  omega

theorem prefixDarts_nodup (k : Fin B.darts.length) : (prefixDarts M B k).Nodup := by
  rw [prefixDarts, List.nodup_cons]
  have hnd : (B.darts.take k.val).Nodup := B.nodup.take
  refine ⟨?_, hnd.map (embed_injective M)⟩
  rw [List.mem_map]
  rintro ⟨d, _, h⟩
  cases h

theorem suffixDarts_nodup (k : Fin B.darts.length) : (suffixDarts M B k).Nodup := by
  rw [suffixDarts, List.nodup_cons]
  have hnd : (B.darts.drop k.val).Nodup := B.nodup.drop
  refine ⟨?_, hnd.map (embed_injective M)⟩
  rw [List.mem_map]
  rintro ⟨d, _, h⟩
  cases h

theorem prefixDarts_chain (k : Fin B.darts.length) :
    (prefixDarts M B k).IsChain (fun d e : Dart M => (splitMap M B k).facePerm d = e) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hk := k.isLt
  have hi' : i < k.val := by simpa [prefixDarts, List.length_take, min_eq_left hk.le] using hi
  cases i with
  | zero =>
      simp only [prefixDarts, List.getElem_cons_zero, List.getElem_cons_succ,
        List.getElem_map, List.getElem_take]
      change (splitMap M B k).facePerm none = embed M (B.darts[0])
      exact facePerm_none_of_ne M _ _ (corners_ne M B k hi')
  | succ i =>
      simp only [prefixDarts, List.getElem_cons_succ, List.getElem_map, List.getElem_take]
      change (splitMap M B k).facePerm (embed M (B.darts[i])) = embed M (B.darts[i + 1])
      have hstep := (List.isChain_iff_getElem.mp B.chain) i (by omega)
      change (toCombMap M (firstCorner M B) (secondCorner M B k)).facePerm _ = _
      rw [facePerm_embed_other M _ _ _ (by
        rw [hstep]
        exact corner_get_ne M B ⟨i + 1, by omega⟩ ⟨0, List.length_pos_iff.mpr B.nonempty⟩ (by
          change i + 1 ≠ 0; omega)) (by
        rw [hstep]
        exact corner_get_ne M B ⟨i + 1, by omega⟩ k (by change i + 1 ≠ k.val; omega)), hstep]

theorem suffixDarts_chain (k : Fin B.darts.length) :
    (suffixDarts M B k).IsChain (fun d e : Dart M => (splitMap M B k).facePerm d = e) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hk := k.isLt
  have hi' : k.val + i < B.darts.length := by
    simp only [suffixDarts, List.length_cons, List.length_map, List.length_drop] at hi
    omega
  cases i with
  | zero =>
      simp only [suffixDarts, List.getElem_cons_zero, List.getElem_cons_succ,
        List.getElem_map, List.getElem_drop, Nat.add_zero]
      change (splitMap M B k).facePerm (some none) = embed M (B.darts[k.val])
      exact facePerm_positive M _ _
  | succ i =>
      simp only [suffixDarts, List.getElem_cons_succ, List.getElem_map, List.getElem_drop]
      change (splitMap M B k).facePerm (embed M (B.darts[k.val + i])) =
        embed M (B.darts[k.val + (i + 1)])
      have hstep : M.facePerm (B.darts[k.val + i]) = B.darts[k.val + (i + 1)] :=
        (List.isChain_iff_getElem.mp B.chain) (k.val + i) (by omega)
      change (toCombMap M (firstCorner M B) (secondCorner M B k)).facePerm _ = _
      rw [facePerm_embed_other M _ _ _ (by
        rw [hstep]
        exact corner_get_ne M B ⟨k.val + (i + 1), by omega⟩
          ⟨0, List.length_pos_iff.mpr B.nonempty⟩ (by change k.val + (i + 1) ≠ 0; omega)) (by
        rw [hstep]
        exact corner_get_ne M B ⟨k.val + (i + 1), by omega⟩ k (by
          change k.val + (i + 1) ≠ k.val; omega)), hstep]

theorem prefixDarts_closes (k : Fin B.darts.length) :
    (splitMap M B k).facePerm ((prefixDarts M B k).getLast (List.cons_ne_nil _ _)) =
      (prefixDarts M B k).head (List.cons_ne_nil _ _) := by
  have hklt := k.isLt
  by_cases hk : k.val = 0
  · have hcorner : secondCorner M B k = firstCorner M B := by
      apply congrArg B.darts.get
      exact Fin.ext hk
    simp only [prefixDarts, hk, List.take_zero, List.map_nil, List.getLast_singleton,
      List.head_cons]
    change (toCombMap M (firstCorner M B) (secondCorner M B k)).facePerm none = none
    rw [hcorner]
    exact facePerm_none_of_eq M _
  · have htake : B.darts.take k.val ≠ [] := by
      apply List.length_pos_iff.mp
      rw [List.length_take, min_eq_left hklt.le]
      omega
    have hmap : (B.darts.take k.val).map (embed M) ≠ [] := by
      intro h
      exact htake (List.map_eq_nil_iff.mp h)
    have hlast : (B.darts.take k.val).getLast htake = B.darts[k.val - 1] := by
      simp only [List.getLast_eq_getElem, List.getElem_take, List.length_take,
        min_eq_left hklt.le]
    change (splitMap M B k).facePerm
      ((none :: (B.darts.take k.val).map (embed M)).getLast _) = none
    rw [List.getLast_cons hmap, List.getLast_map, hlast]
    have hstep : M.facePerm (B.darts[k.val - 1]) = secondCorner M B k := by
      have h := (List.isChain_iff_getElem.mp B.chain) (k.val - 1) (by omega)
      simpa only [show k.val - 1 + 1 = k.val by omega, secondCorner, List.get_eq_getElem] using h
    exact facePerm_embed_right M _ _ _
      (by rw [hstep]; exact (corners_ne M B k (by omega)).symm) hstep

theorem suffixDarts_closes (k : Fin B.darts.length) :
    (splitMap M B k).facePerm ((suffixDarts M B k).getLast (List.cons_ne_nil _ _)) =
      (suffixDarts M B k).head (List.cons_ne_nil _ _) := by
  have hdrop : B.darts.drop k.val ≠ [] := by
    intro h
    have hlen := List.drop_eq_nil_iff.mp h
    exact (Nat.not_le_of_gt k.isLt) hlen
  have hmap : (B.darts.drop k.val).map (embed M) ≠ [] := by
    intro h
    exact hdrop (List.map_eq_nil_iff.mp h)
  change (splitMap M B k).facePerm
    ((some none :: (B.darts.drop k.val).map (embed M)).getLast _) = some none
  rw [List.getLast_cons hmap, List.getLast_map, List.getLast_drop]
  apply facePerm_embed_left
  simpa only [firstCorner, List.get_eq_getElem, List.head_eq_getElem] using B.closes

noncomputable def prefixBoundary (k : Fin B.darts.length) :
    FaceBoundary (splitMap M B k) ((splitMap M B k).faceOf none) :=
  FaceBoundary.ofCyclicList (splitMap M B k) (prefixDarts M B k)
    (List.cons_ne_nil _ _) (prefixDarts_nodup M B k) (prefixDarts_chain M B k)
    (prefixDarts_closes M B k)

noncomputable def suffixBoundary (k : Fin B.darts.length) :
    FaceBoundary (splitMap M B k) ((splitMap M B k).faceOf (some none)) :=
  FaceBoundary.ofCyclicList (splitMap M B k) (suffixDarts M B k)
    (List.cons_ne_nil _ _) (suffixDarts_nodup M B k) (suffixDarts_chain M B k)
    (suffixDarts_closes M B k)

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.prefixDarts_chain
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.suffixDarts_chain
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.prefixBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.suffixBoundary
