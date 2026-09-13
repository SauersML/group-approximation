import GroupApproximation.GGT.HullSCLemma51LetterPullbackCutOutcomeSides

/-!
# Outcomes of the certificate cut: the right side and the case split

* `CutMove.outcome_right`: the arc of a cut move runs through the unknown letter and a peripheral
  letter of the right side reads at its coset; that letter is designated.
* `CutMove.outcome`: every cut move gives a pullback outcome.  Either the unknown letter lies after
  the arc (`CutMove.outcome_before`), or it lies in the arc and a side letter reads at its coset
  (`CutMove.outcome_left`, `CutMove.outcome_right`), or it lies in the arc, no side letter reads
  at its coset, and it has a bounded value (`CutMove.mem_image_of_inner`).
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))} {D : GGT.RelGenSet G Lambda} {q : G →* Q}
  {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
  {L arc R ext rem x y tail : List (GGT.RelLetter G Lambda)}

/-- **A designated letter in the right side.** -/
theorem CutMove.outcome_right (hm : CutMove W D q hq lam h c L arc R ext rem x y tail)
    {r N n : ℕ} (hr1 : 1 ≤ r) (hr : L.length + arc.length + R.length + ext.length ≤ r)
    (hN : r + 1 ≤ N) (hn : arc.length + tail.length ≤ n + 2)
    {y₁ : List (GGT.RelLetter G Lambda)} (harc : arc = x ++ GGT.RelLetter.comp lam h⁻¹ :: y₁)
    (hy : y = y₁ ++ tail) {j : ℕ} (hj : j < R.length) (hjc : GGT.RelLetter.IsCompOf lam R[j])
    (hcos : (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
      GGT.RelLetter.listVal (R.take j))⁻¹ *
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x) ∈ D.fam lam) :
    PullbackOutcome D q hq lam (pullbackAtoms W D lam r) N h n := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨word, hword, hsub⟩ := hm.rem_sub
  have hxa : x.length < arc.length := by
    rw [harc, List.length_append, List.length_cons]
    omega
  have hget : arc[x.length] = GGT.RelLetter.comp lam h⁻¹ := List.getElem_of_append harc rfl
  have hv : arc[x.length].val = h⁻¹ := congrArg GGT.RelLetter.val hget
  have htake : arc.take x.length = x := by
    rw [harc]
    exact List.take_left
  have hkc : GGT.RelLetter.IsCompOf lam arc[x.length] := by
    rw [hget]
    exact rfl
  have hRj := listVal_take_mul_getElem_mul_drop R hj
  have hcos' : (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take j))⁻¹ *
      GGT.RelLetter.listVal x ∈ D.fam lam := by
    have e : (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take j))⁻¹ *
        GGT.RelLetter.listVal x = (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
          GGT.RelLetter.listVal (R.take j))⁻¹ *
          (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x) := by
      group
    rw [e]
    exact hcos
  have hLk : ∀ (k : ℕ) (hk : k < L.length),
      (GGT.RelLetter.IsCompOf lam L[k] ∨ ∃ z : G, L[k] = GGT.RelLetter.base z ∧ z ∈ D.fam lam) →
        c⁻¹ * q ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal (L.take k)) ∈
          (D.mapSurjective q hq).fam lam →
          (invLetter D L[k]).val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
    intro k hk hshape hv'
    refine invLetter_val_mem_boundedProducts W D lam hr1 hN1
      (hm.face.left_adm _ (List.getElem_mem hk)) hshape fun hc => ?_
    refine hm.face.left_val_mem_of_arc lam hr1 hr hN hk hc (hm.lift.arc_mid _ harc hy hv' ?_)
    intro hno
    have e : (GGT.RelLetter.listVal (L.take k))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
          GGT.RelLetter.listVal (R.take j)) =
        ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal (L.take k))⁻¹ *
          GGT.RelLetter.listVal x *
          ((GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take j))⁻¹ *
            GGT.RelLetter.listVal x)⁻¹ := by
      group
    have hcross : (GGT.RelLetter.listVal (L.take k))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
          GGT.RelLetter.listVal (R.take j)) ∈ D.fam lam := by
      rw [e]
      exact mul_mem hno (inv_mem hcos')
    exact false_of_crossCoset D hm.face.arc_geo hm.face.short hm.face.left_adm
      hm.face.right_adm hk hj hc hcross
  have hRk : ∀ (k : ℕ) (hk : k < R.length), k ≠ j →
      (GGT.RelLetter.IsCompOf lam R[k] ∨ ∃ z : G, R[k] = GGT.RelLetter.base z ∧ z ∈ D.fam lam) →
        c⁻¹ * q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take k)) ∈
          (D.mapSurjective q hq).fam lam →
          (invLetter D R[k]).val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
    intro k hk hkj hshape hv'
    refine invLetter_val_mem_boundedProducts W D lam hr1 hN1
      (hm.face.right_adm _ (List.getElem_mem hk)) hshape fun hc => ?_
    refine hm.face.right_val_mem_of_arc lam hr1 hr hN hk hc (hm.lift.arc_mid _ harc hy hv' ?_)
    intro hno
    have e : (GGT.RelLetter.listVal (R.take k))⁻¹ * GGT.RelLetter.listVal (R.take j) =
        (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take k))⁻¹ *
          (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take j)) := by
      group
    have hkj' : (GGT.RelLetter.listVal (R.take k))⁻¹ * GGT.RelLetter.listVal (R.take j) ∈
        D.fam lam := by
      rw [e]
      exact inv_mul_mem_of_common_right hno hcos'
    exact hkj (eq_of_isCompOf_coset_of_isRelGeodesic D hm.face.right_adm hm.face.right_geo hk hj
      hc hjc hkj')
  have hnull : GGT.RelLetter.listVal ((respellInv D L ++ (respellInv D rem ++
      respellInv D (R.drop (j + 1)))) ++ invLetter D R[j] ::
      (respellInv D (R.take j) ++ tail)) =
      (GGT.RelLetter.listVal L)⁻¹ * (GGT.RelLetter.listVal rem)⁻¹ *
        (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R)⁻¹ *
        (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal tail) := by
    simp only [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_cons,
      listVal_respellInv, val_invLetter]
    rw [← hRj]
    group
  have hstart : q (GGT.RelLetter.listVal (respellInv D L ++ (respellInv D rem ++
      respellInv D (R.drop (j + 1)))) * (invLetter D R[j]).val) =
      q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take j)) := by
    have e1 : GGT.RelLetter.listVal (respellInv D L ++ (respellInv D rem ++
        respellInv D (R.drop (j + 1)))) * (invLetter D R[j]).val =
        (GGT.RelLetter.listVal L)⁻¹ * (GGT.RelLetter.listVal rem)⁻¹ *
          ((GGT.RelLetter.listVal (R.drop (j + 1)))⁻¹ * R[j].val⁻¹) := by
      simp only [GGT.OsinComponents.listVal_append, listVal_respellInv, val_invLetter]
      group
    have e2 : GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take j) =
        GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R *
          ((GGT.RelLetter.listVal (R.drop (j + 1)))⁻¹ * R[j].val⁻¹) := by
      rw [← hRj]
      group
    rw [e1, e2, map_mul q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R),
      hm.quot_arc_R, ← map_mul]
  have hcosz : c⁻¹ * q (GGT.RelLetter.listVal (respellInv D L ++ (respellInv D rem ++
      respellInv D (R.drop (j + 1))))) ∈ (D.mapSurjective q hq).fam lam := by
    have e1 : GGT.RelLetter.listVal (respellInv D L ++ (respellInv D rem ++
        respellInv D (R.drop (j + 1)))) =
        (GGT.RelLetter.listVal L)⁻¹ * (GGT.RelLetter.listVal rem)⁻¹ *
          (GGT.RelLetter.listVal (R.drop (j + 1)))⁻¹ := by
      simp only [GGT.OsinComponents.listVal_append, listVal_respellInv]
      group
    have e2 : GGT.RelLetter.listVal x * ((GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
        GGT.RelLetter.listVal (R.take j))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x))⁻¹ * R[j].val =
        GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R *
          (GGT.RelLetter.listVal (R.drop (j + 1)))⁻¹ := by
      rw [← hRj]
      group
    have hq1 : q (GGT.RelLetter.listVal (respellInv D L ++ (respellInv D rem ++
        respellInv D (R.drop (j + 1))))) =
        q (GGT.RelLetter.listVal x * ((GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
          GGT.RelLetter.listVal (R.take j))⁻¹ *
          (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x))⁻¹) * q R[j].val := by
      rw [e1, map_mul q ((GGT.RelLetter.listVal L)⁻¹ * (GGT.RelLetter.listVal rem)⁻¹),
        ← hm.quot_arc_R, ← map_mul, ← map_mul, e2]
    rw [hq1, ← mul_assoc, map_mul, ← mul_assoc]
    exact mul_mem (mul_mem hm.lift.coset (Subgroup.mem_map_of_mem q (inv_mem hcos)))
      (Subgroup.mem_map_of_mem q
        (val_mem_fam_of_isCompOf (hm.face.right_adm _ (List.getElem_mem hj)) hjc))
  have hcosk : (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
      GGT.RelLetter.listVal (R.take j))⁻¹ *
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal (arc.take x.length)) ∈ D.fam lam := by
    rw [htake]
    exact hcos
  obtain ⟨X, Y, hX, hY, hXY⟩ := hm.face.right_designated lam hr1 hr hN hj hjc hxa hkc hcosk
  have hB1 := cosetLettersAt_respellInv_take_mapHom D q hq lam
    (boundedProducts (pullbackAtoms W D lam r) N) c (GGT.RelLetter.listVal arc)
    hm.face.right_adm j hRk
  have hB2 := hm.lift.tail_mid (q '' boundedProducts (pullbackAtoms W D lam r) N) harc hy
  have hB3 := cosetLettersAt_respellInv_mapHom D q hq lam _ c (GGT.RelLetter.listVal L)⁻¹
    hm.face.left_adm hLk
  have hB4 := cosetLettersAt_respellInv_rem_mapHom W D q hq lam hr1 hN1 c
    ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal L *
      GGT.RelLetter.listVal (respellInv D L)) hm.rem_letters hword hsub
  have hB5 := cosetLettersAt_respellInv_drop_mapHom D q hq lam
    (boundedProducts (pullbackAtoms W D lam r) N) c (GGT.RelLetter.listVal arc)
    hm.face.right_adm j hRk
  have hx12 : q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take j) *
      GGT.RelLetter.listVal (respellInv D (R.take j))) = q (GGT.RelLetter.listVal arc) := by
    rw [listVal_respellInv, mul_inv_cancel_right]
  have hx23 : q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal tail) =
      q ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal L) := by
    rw [hm.quot_arc_tail, inv_mul_cancel, map_one]
  have hx45 : q ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal L *
      GGT.RelLetter.listVal (respellInv D L) * GGT.RelLetter.listVal (respellInv D rem)) =
      q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R) := by
    rw [hm.quot_arc_R, listVal_respellInv, listVal_respellInv, mul_inv_cancel_right]
  refine Or.inr ⟨respellInv D L ++ (respellInv D rem ++ respellInv D (R.drop (j + 1))),
    respellInv D (R.take j) ++ tail, invLetter D R[j], c, ?_, ?_, ?_, ?_, hcosz,
    ⟨X, Y, hX, hY, Or.inr (by rw [val_invLetter, hXY, hv])⟩, ?_⟩
  · intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with (ha | ha | ha) | ha | ha | ha
    · exact isLetter_respellInv D hm.face.left_adm a ha
    · exact isLetter_respellInv D hm.rem_letters a ha
    · exact isLetter_respellInv D
        (fun b hb => hm.face.right_adm b (List.mem_of_mem_drop hb)) a ha
    · rw [ha]
      exact isLetter_invLetter D (hm.face.right_adm _ (List.getElem_mem hj))
    · exact isLetter_respellInv D
        (fun b hb => hm.face.right_adm b (List.mem_of_mem_take hb)) a ha
    · exact hm.tail_letters a ha
  · rw [hnull, map_mul, map_mul, ← hm.quot_arc_R, hm.quot_arc_tail, mul_one, map_inv,
      mul_inv_cancel]
  · simp only [List.length_append, length_respellInv, List.length_take, List.length_drop]
    have hs := hm.short
    omega
  · obtain ⟨mu, g, he⟩ := exists_eq_comp_of_isCompOf hjc
    rw [he] at hjc ⊢
    exact hjc
  · rw [hstart]
    simp only [List.append_assoc]
    exact CosetLettersAt.append_mapHom hB1 (CosetLettersAt.append_mapHom hB2
      (CosetLettersAt.append_mapHom hB3 (CosetLettersAt.append_mapHom hB4 hB5 hx45) rfl) hx23)
      hx12

/-- **Every cut move gives a pullback outcome.** -/
theorem CutMove.outcome (hm : CutMove W D q hq lam h c L arc R ext rem x y tail)
    {r N n : ℕ} (hr1 : 1 ≤ r) (hr : L.length + arc.length + R.length + ext.length ≤ r)
    (hN : r + 1 ≤ N) (hn : arc.length + tail.length ≤ n + 2) :
    PullbackOutcome D q hq lam (pullbackAtoms W D lam r) N h n := by
  rcases List.append_eq_append_iff.mp hm.split with ⟨x', hx, ht⟩ | ⟨bs, harc, hbs⟩
  · exact hm.outcome_before hr1 hr hN hn hx ht
  rcases List.cons_eq_append_iff.mp hbs with ⟨rfl, ht⟩ | ⟨y₁, rfl, hy⟩
  · refine hm.outcome_before hr1 hr hN hn (x' := []) ?_ ?_
    · rw [harc, List.append_nil, List.append_nil]
    · rw [ht, List.nil_append]
  by_cases hL : ∃ (j : ℕ) (hj : j < L.length), GGT.RelLetter.IsCompOf lam L[j] ∧
      (GGT.RelLetter.listVal (L.take j))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x) ∈ D.fam lam
  · obtain ⟨j, hj, hjc, hcos⟩ := hL
    exact hm.outcome_left hr1 hr hN hn harc hy hj hjc hcos
  by_cases hR : ∃ (j : ℕ) (hj : j < R.length), GGT.RelLetter.IsCompOf lam R[j] ∧
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
        GGT.RelLetter.listVal (R.take j))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x) ∈ D.fam lam
  · obtain ⟨j, hj, hjc, hcos⟩ := hR
    exact hm.outcome_right hr1 hr hN hn harc hy hj hjc hcos
  exact Or.inl (hm.mem_image_of_inner hr1 hr hN harc
    (fun j hj hjc hcos => hL ⟨j, hj, hjc, hcos⟩) (fun j hj hjc hcos => hR ⟨j, hj, hjc, hcos⟩))

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.CutMove.outcome_right
#audit_axioms GroupApproximation.HullSC.CutMove.outcome
