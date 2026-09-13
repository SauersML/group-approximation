import GroupApproximation.GGT.HullSCLemma51LetterPullbackCutFaces

/-!
# The side letters of the certificate cut

The closed word `L ++ arc ++ R ++ respellInv ext` of a cut face (`CutFace`) carries the
peripheral letters of the new quotient-null word.  By geodesicity each of `L`, `arc`, `R` has at
most one peripheral letter of index `λ` in a coset, and `false_of_crossCoset` keeps `L` and `R`
apart.  The arc letters at a coset are the only unknown.

* `CutFace.left_val_mem`, `CutFace.right_val_mem`: a side letter with no arc letter at its coset
  has a bounded value.
* `CutFace.arc_val_mem`: an arc letter with no side letter at its coset has a bounded value.
* `CutFace.left_designated`, `CutFace.right_designated`: a side letter sharing its coset with an
  arc letter `b` has inverse value `X · b.val · Y` for bounded products `X`, `Y`.
-/

namespace GroupApproximation
namespace HullSC

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A letter of `L` with no arc letter at its coset** has a bounded value. -/
theorem CutFace.left_val_mem {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {L arc R ext : List (GGT.RelLetter G Lambda)}
    (hcf : CutFace W D L arc R ext) (lam : Lambda) {r N : ℕ} (hr1 : 1 ≤ r)
    (hr : L.length + arc.length + R.length + ext.length ≤ r) (hN : r + 1 ≤ N) {i : ℕ}
    (hi : i < L.length) (hcomp : GGT.RelLetter.IsCompOf lam L[i])
    (harc : CosetLettersAt D lam (pullbackAtoms W D lam r) (GGT.RelLetter.listVal (L.take i))
      (GGT.RelLetter.listVal L) arc) :
    L[i].val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have hLi := listVal_take_mul_getElem_mul_drop L hi
  refine val_mem_boundedProducts_of_face W D lam (u := L.take i)
    (v := L.drop (i + 1) ++ (arc ++ (R ++ respellInv D ext))) (a := L[i])
    (fun b hb => hcf.left_adm b (List.mem_of_mem_take hb)) ?_ ?_
    (val_mem_fam_of_isCompOf (hcf.left_adm _ (List.getElem_mem hi)) hcomp) ?_ ?_ ?_ hN
  · intro b hb
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb | hb
    · exact hcf.left_adm b (List.mem_of_mem_drop hb)
    · exact hcf.arc_adm b hb
    · exact hcf.right_adm b hb
    · exact hcf.ext_letters b hb
  · rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_append,
      GGT.OsinComponents.listVal_append, listVal_respellInv, hcf.value, ← hLi]
    group
  · have h := cosetLettersAt_take_of_isRelGeodesic D lam (pullbackAtoms W D lam r) hcf.left_adm
      hcf.left_geo hi hcomp 1 le_rfl
    rwa [one_mul] at h
  · have hdrop := cosetLettersAt_drop_of_isRelGeodesic D lam (pullbackAtoms W D lam r)
      hcf.left_adm hcf.left_geo hi hcomp 1 (k := i + 1) (by omega)
    rw [one_mul, one_mul, listVal_take_succ L hi] at hdrop
    have hR : CosetLettersAt D lam (pullbackAtoms W D lam r) (GGT.RelLetter.listVal (L.take i))
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc) R := by
      intro j hj _ hv
      exact (false_of_crossCoset D hcf.arc_geo hcf.short hcf.left_adm hcf.right_adm hi hj hcomp
        hv).elim
    refine hdrop.append ?_
    rw [hLi]
    exact harc.append (hR.append (hcf.ext_block lam hr1 _))
  · simp only [List.length_append, List.length_take, List.length_drop, length_respellInv]
    omega

/-- **A letter of `R` with no arc letter at its coset** has a bounded value. -/
theorem CutFace.right_val_mem {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {L arc R ext : List (GGT.RelLetter G Lambda)}
    (hcf : CutFace W D L arc R ext) (lam : Lambda) {r N : ℕ} (hr1 : 1 ≤ r)
    (hr : L.length + arc.length + R.length + ext.length ≤ r) (hN : r + 1 ≤ N) {i : ℕ}
    (hi : i < R.length) (hcomp : GGT.RelLetter.IsCompOf lam R[i])
    (harc : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take i))
      (GGT.RelLetter.listVal L) arc) :
    R[i].val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have hRi := listVal_take_mul_getElem_mul_drop R hi
  have hu : GGT.RelLetter.listVal (L ++ (arc ++ R.take i)) =
      GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
        GGT.RelLetter.listVal (R.take i) := by
    rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_append, mul_assoc]
  refine val_mem_boundedProducts_of_face W D lam (u := L ++ (arc ++ R.take i))
    (v := R.drop (i + 1) ++ respellInv D ext) (a := R[i]) ?_ ?_ ?_
    (val_mem_fam_of_isCompOf (hcf.right_adm _ (List.getElem_mem hi)) hcomp) ?_ ?_ ?_ hN
  · intro b hb
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb
    · exact hcf.left_adm b hb
    · exact hcf.arc_adm b hb
    · exact hcf.right_adm b (List.mem_of_mem_take hb)
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hcf.right_adm b (List.mem_of_mem_drop hb)
    · exact hcf.ext_letters b hb
  · rw [hu, GGT.OsinComponents.listVal_append, listVal_respellInv, hcf.value, ← hRi]
    group
  · rw [hu]
    have hL : CosetLettersAt D lam (pullbackAtoms W D lam r)
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take i))
        1 L := by
      intro t ht htc hv
      refine (false_of_crossCoset D hcf.arc_geo hcf.short hcf.left_adm hcf.right_adm ht hi htc
        ?_).elim
      have e : (GGT.RelLetter.listVal (L.take t))⁻¹ * (GGT.RelLetter.listVal L *
          GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take i)) =
          ((GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
            GGT.RelLetter.listVal (R.take i))⁻¹ * (1 * GGT.RelLetter.listVal (L.take t)))⁻¹ := by
        group
      rw [e]
      exact inv_mem hv
    refine hL.append ?_
    rw [one_mul]
    exact harc.append (cosetLettersAt_take_of_isRelGeodesic D lam _ hcf.right_adm
      hcf.right_geo hi hcomp _ le_rfl)
  · rw [hu]
    have hdrop := cosetLettersAt_drop_of_isRelGeodesic D lam (pullbackAtoms W D lam r)
      hcf.right_adm hcf.right_geo hi hcomp (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc)
      (k := i + 1) (by omega)
    rw [listVal_take_succ R hi, ← mul_assoc] at hdrop
    refine hdrop.append ?_
    have e : GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
        GGT.RelLetter.listVal (R.take i) * R[i].val * GGT.RelLetter.listVal (R.drop (i + 1)) =
        GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R := by
      rw [← hRi]
      simp only [mul_assoc]
    rw [e]
    exact hcf.ext_block lam hr1 _
  · simp only [List.length_append, List.length_take, List.length_drop, length_respellInv]
    omega

/-- **An arc letter with no side letter at its coset** has a bounded value. -/
theorem CutFace.arc_val_mem {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {L arc R ext : List (GGT.RelLetter G Lambda)}
    (hcf : CutFace W D L arc R ext) (lam : Lambda) {r N : ℕ} (hr1 : 1 ≤ r)
    (hr : L.length + arc.length + R.length + ext.length ≤ r) (hN : r + 1 ≤ N) {k : ℕ}
    (hk : k < arc.length) (hcomp : GGT.RelLetter.IsCompOf lam arc[k])
    (hL : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal (arc.take k)) 1 L)
    (hR : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal (arc.take k))
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc) R) :
    arc[k].val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have harck := listVal_take_mul_getElem_mul_drop arc hk
  have hu : GGT.RelLetter.listVal (L ++ arc.take k) =
      GGT.RelLetter.listVal L * GGT.RelLetter.listVal (arc.take k) := by
    rw [GGT.OsinComponents.listVal_append]
  refine val_mem_boundedProducts_of_face W D lam (u := L ++ arc.take k)
    (v := arc.drop (k + 1) ++ (R ++ respellInv D ext)) (a := arc[k]) ?_ ?_ ?_
    (val_mem_fam_of_isCompOf (hcf.arc_adm _ (List.getElem_mem hk)) hcomp) ?_ ?_ ?_ hN
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hcf.left_adm b hb
    · exact hcf.arc_adm b (List.mem_of_mem_take hb)
  · intro b hb
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb
    · exact hcf.arc_adm b (List.mem_of_mem_drop hb)
    · exact hcf.right_adm b hb
    · exact hcf.ext_letters b hb
  · rw [hu, GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_append,
      listVal_respellInv, hcf.value, ← harck]
    group
  · rw [hu]
    refine hL.append ?_
    rw [one_mul]
    exact cosetLettersAt_take_of_isRelGeodesic D lam _ hcf.arc_adm hcf.arc_geo hk hcomp _ le_rfl
  · rw [hu]
    have hdrop := cosetLettersAt_drop_of_isRelGeodesic D lam (pullbackAtoms W D lam r)
      hcf.arc_adm hcf.arc_geo hk hcomp (GGT.RelLetter.listVal L) (k := k + 1) (by omega)
    rw [listVal_take_succ arc hk, ← mul_assoc] at hdrop
    refine hdrop.append ?_
    have e : GGT.RelLetter.listVal L * GGT.RelLetter.listVal (arc.take k) * arc[k].val *
        GGT.RelLetter.listVal (arc.drop (k + 1)) =
        GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc := by
      rw [← harck]
      simp only [mul_assoc]
    rw [e]
    exact hR.append (hcf.ext_block lam hr1 _)
  · simp only [List.length_append, List.length_take, List.length_drop, length_respellInv]
    omega

-- DESIGNATED

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.CutFace.left_val_mem
#audit_axioms GroupApproximation.HullSC.CutFace.right_val_mem
#audit_axioms GroupApproximation.HullSC.CutFace.arc_val_mem
