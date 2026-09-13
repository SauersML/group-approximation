import GroupApproximation.GGT.HullSCLemma51LetterPullbackCutBlocks

/-!
# Outcomes of the certificate cut

A quotient-null word `p ++ [comp λ h⁻¹]` all of whose rotations are relative geodesics admits the
certificate cut: a rotation `arc ++ tail` of the word, a relator `ext ++ rem ∈ W` and side words
`L`, `R` with `listVal ext = L · arc · R` and `|L| + |rem| + |R| < |arc|`.  The cut move replaces
the arc by the respelled inverses of `L`, `rem` and `R` (`CutMove`).

* `CutMove.outcome_before`: when the arc lies before the unknown letter, the new word is a
  shorter quotient-null word through the unknown letter.
* `CutMove.mem_image_of_inner`: when the arc runs through the unknown letter and no peripheral
  letter of a side word reads at its coset, `h` is a bounded product.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- The coset relation is symmetric. -/
theorem inv_mul_mem_symm {H : Subgroup G} {a b : G} (hab : a⁻¹ * b ∈ H) : b⁻¹ * a ∈ H := by
  have h' := H.inv_mem hab
  rwa [mul_inv_rev, inv_inv] at h'

/-- **The data of one cut move**: a certificate cut face with the rest `rem` of its relator, and
a rotated lift `x ++ comp λ h⁻¹ :: y` of the word, spelled as `arc ++ tail`. -/
structure CutMove (W : Set (List (GGT.RelLetter G Lambda))) (D : GGT.RelGenSet G Lambda)
    (q : G →* Q) (hq : Function.Surjective q) (lam : Lambda) (h : G) (c : Q)
    (L arc R ext rem x y tail : List (GGT.RelLetter G Lambda)) : Prop where
  face : CutFace W D L arc R ext
  rem_letters : ∀ a ∈ rem, D.IsLetter a
  rem_sub : ∃ word ∈ W, ∀ a ∈ rem, a ∈ word
  null : q (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R *
    GGT.RelLetter.listVal rem) = 1
  short : L.length + rem.length + R.length < arc.length
  lift : RotatedLift D q hq lam h c x y
  split : arc ++ tail = x ++ GGT.RelLetter.comp lam h⁻¹ :: y

variable {W : Set (List (GGT.RelLetter G Lambda))} {D : GGT.RelGenSet G Lambda} {q : G →* Q}
  {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
  {L arc R ext rem x y tail : List (GGT.RelLetter G Lambda)}

/-- The arc and the right side have the image of the inverted left side and rest. -/
theorem CutMove.quot_arc_R (hm : CutMove W D q hq lam h c L arc R ext rem x y tail) :
    q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R) =
      q ((GGT.RelLetter.listVal L)⁻¹ * (GGT.RelLetter.listVal rem)⁻¹) := by
  have e : GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R =
      (GGT.RelLetter.listVal L)⁻¹ * (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
        GGT.RelLetter.listVal R * GGT.RelLetter.listVal rem) * (GGT.RelLetter.listVal rem)⁻¹ := by
    group
  rw [e, map_mul, map_mul, hm.null, mul_one, ← map_mul]

/-- The rotated word is null in the quotient. -/
theorem CutMove.quot_arc_tail (hm : CutMove W D q hq lam h c L arc R ext rem x y tail) :
    q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal tail) = 1 := by
  rw [← GGT.OsinComponents.listVal_append, hm.split]
  exact hm.lift.null

/-- The lifted word is null in the quotient. -/
theorem CutMove.quot_null (hm : CutMove W D q hq lam h c L arc R ext rem x y tail) :
    q (GGT.RelLetter.listVal x * h⁻¹ * GGT.RelLetter.listVal y) = 1 := by
  have hnull := hm.lift.null
  rwa [listVal_append_comp_cons] at hnull

theorem CutMove.tail_letters (hm : CutMove W D q hq lam h c L arc R ext rem x y tail) :
    ∀ a ∈ tail, D.IsLetter a := fun a ha =>
  hm.lift.letters a (by rw [← hm.split]; exact List.mem_append.mpr (Or.inr ha))

/-- **The arc before the unknown letter.**  The new word `S ++ x' ++ comp λ h⁻¹ :: y`, with `S`
the respelled inverses of `L`, `rem` and `R`, is quotient-null and shorter. -/
theorem CutMove.outcome_before (hm : CutMove W D q hq lam h c L arc R ext rem x y tail)
    {r N n : ℕ} (hr1 : 1 ≤ r) (hr : L.length + arc.length + R.length + ext.length ≤ r)
    (hN : r + 1 ≤ N) (hn : arc.length + tail.length ≤ n + 2)
    {x' : List (GGT.RelLetter G Lambda)} (hx : x = arc ++ x')
    (ht : tail = x' ++ GGT.RelLetter.comp lam h⁻¹ :: y) :
    PullbackOutcome D q hq lam (pullbackAtoms W D lam r) N h n := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨word, hword, hsub⟩ := hm.rem_sub
  have hval : q (GGT.RelLetter.listVal
      (respellInv D L ++ (respellInv D rem ++ (respellInv D R ++ x')))) =
      q (GGT.RelLetter.listVal x) := by
    simp only [GGT.OsinComponents.listVal_append, listVal_respellInv]
    have e : (GGT.RelLetter.listVal L)⁻¹ * ((GGT.RelLetter.listVal rem)⁻¹ *
        ((GGT.RelLetter.listVal R)⁻¹ * GGT.RelLetter.listVal x')) =
        (GGT.RelLetter.listVal L)⁻¹ * (GGT.RelLetter.listVal rem)⁻¹ *
          ((GGT.RelLetter.listVal R)⁻¹ * GGT.RelLetter.listVal x') := by
      group
    rw [e, map_mul, ← hm.quot_arc_R, ← map_mul, hx, GGT.OsinComponents.listVal_append]
    congr 1
    group
  have hnull := hm.quot_null
  have htl : tail.length = x'.length + y.length + 1 := by
    rw [ht, List.length_append, List.length_cons]
    omega
  have hLval : ∀ (k : ℕ) (hk : k < L.length),
      (GGT.RelLetter.IsCompOf lam L[k] ∨ ∃ z : G, L[k] = GGT.RelLetter.base z ∧ z ∈ D.fam lam) →
        c⁻¹ * q ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal (L.take k)) ∈
          (D.mapSurjective q hq).fam lam →
          (invLetter D L[k]).val ∈ boundedProducts (pullbackAtoms W D lam r) N :=
    fun k hk hshape hv =>
      invLetter_val_mem_boundedProducts W D lam hr1 hN1
        (hm.face.left_adm _ (List.getElem_mem hk)) hshape fun hc =>
          hm.face.left_val_mem_of_arc lam hr1 hr hN hk hc (hm.lift.arc_left _ hx hv)
  have hRval : ∀ (k : ℕ) (hk : k < R.length),
      (GGT.RelLetter.IsCompOf lam R[k] ∨ ∃ z : G, R[k] = GGT.RelLetter.base z ∧ z ∈ D.fam lam) →
        c⁻¹ * q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take k)) ∈
          (D.mapSurjective q hq).fam lam →
          (invLetter D R[k]).val ∈ boundedProducts (pullbackAtoms W D lam r) N :=
    fun k hk hshape hv =>
      invLetter_val_mem_boundedProducts W D lam hr1 hN1
        (hm.face.right_adm _ (List.getElem_mem hk)) hshape fun hc =>
          hm.face.right_val_mem_of_arc lam hr1 hr hN hk hc (hm.lift.arc_left _ hx hv)
  have hB1 := cosetLettersAt_of_avoidsFrom (D.mapSurjective q hq) lam
    (q '' boundedProducts (pullbackAtoms W D lam r) N) _ hm.lift.avoid_right
  have hB2 := cosetLettersAt_respellInv_mapHom D q hq lam _ c (GGT.RelLetter.listVal L)⁻¹
    hm.face.left_adm hLval
  have hB3 := cosetLettersAt_respellInv_rem_mapHom W D q hq lam hr1 hN1 c
    ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal L *
      GGT.RelLetter.listVal (respellInv D L)) hm.rem_letters hword hsub
  have hB4 := cosetLettersAt_respellInv_mapHom D q hq lam _ c (GGT.RelLetter.listVal arc)
    hm.face.right_adm hRval
  have hB5 := hm.lift.tail_left (q '' boundedProducts (pullbackAtoms W D lam r) N) hx
  have hx12 : q (GGT.RelLetter.listVal x * h⁻¹ * GGT.RelLetter.listVal y) =
      q ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal L) := by
    rw [inv_mul_cancel, map_one]
    exact hnull
  have hx34 : q ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal L *
      GGT.RelLetter.listVal (respellInv D L) * GGT.RelLetter.listVal (respellInv D rem)) =
      q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R) := by
    rw [hm.quot_arc_R, listVal_respellInv, listVal_respellInv, inv_mul_cancel, one_mul]
  have hx45 : q (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal R *
      GGT.RelLetter.listVal (respellInv D R)) = q (GGT.RelLetter.listVal arc) := by
    rw [listVal_respellInv, mul_inv_cancel_right]
  refine Or.inr ⟨respellInv D L ++ (respellInv D rem ++ (respellInv D R ++ x')), y,
    GGT.RelLetter.comp lam h⁻¹, c, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with ((ha | ha | ha | ha) | ha | ha)
    · exact isLetter_respellInv D hm.face.left_adm a ha
    · exact isLetter_respellInv D hm.rem_letters a ha
    · exact isLetter_respellInv D hm.face.right_adm a ha
    · exact hm.tail_letters a (by rw [ht]; exact List.mem_append.mpr (Or.inl ha))
    · exact hm.lift.letters a (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl ha))))
    · exact hm.lift.letters a (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr ha))))
  · rw [listVal_append_comp_cons, map_mul, map_mul, hval, ← map_mul, ← map_mul]
    exact hnull
  · simp only [List.length_append, length_respellInv]
    have hs := hm.short
    omega
  · rw [hval]
    exact hm.lift.coset
  · exact ⟨1, 1, one_mem_boundedProducts _ _, one_mem_boundedProducts _ _,
      Or.inr (by show h⁻¹ = 1 * h⁻¹ * 1; group)⟩
  · rw [map_mul, hval, ← map_mul]
    exact CosetLettersAt.append_mapHom hB1 (CosetLettersAt.append_mapHom hB2
      (CosetLettersAt.append_mapHom hB3 (CosetLettersAt.append_mapHom hB4 hB5 hx45) hx34) rfl)
      hx12

/-- **The arc through the unknown letter, with no side letter at its coset**: then `h` is a
bounded product. -/
theorem CutMove.mem_image_of_inner (hm : CutMove W D q hq lam h c L arc R ext rem x y tail)
    {r N : ℕ} (hr1 : 1 ≤ r) (hr : L.length + arc.length + R.length + ext.length ≤ r)
    (hN : r + 1 ≤ N) {y₁ : List (GGT.RelLetter G Lambda)}
    (harc : arc = x ++ GGT.RelLetter.comp lam h⁻¹ :: y₁)
    (hL : ∀ (j : ℕ) (hj : j < L.length), GGT.RelLetter.IsCompOf lam L[j] →
      (GGT.RelLetter.listVal (L.take j))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x) ∉ D.fam lam)
    (hR : ∀ (j : ℕ) (hj : j < R.length), GGT.RelLetter.IsCompOf lam R[j] →
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc *
        GGT.RelLetter.listVal (R.take j))⁻¹ *
        (GGT.RelLetter.listVal L * GGT.RelLetter.listVal x) ∉ D.fam lam) :
    q h ∈ q '' boundedProducts (pullbackAtoms W D lam r) N := by
  have hk : x.length < arc.length := by
    rw [harc, List.length_append, List.length_cons]
    omega
  have hget : arc[x.length] = GGT.RelLetter.comp lam h⁻¹ := List.getElem_of_append harc rfl
  have htake : arc.take x.length = x := by
    rw [harc]
    exact List.take_left
  have hcomp : GGT.RelLetter.IsCompOf lam arc[x.length] := by
    rw [hget]
    exact rfl
  have hLc : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal (arc.take x.length)) 1 L := by
    intro j hj hc hv
    rw [htake, one_mul] at hv
    exact (hL j hj hc (inv_mul_mem_symm hv)).elim
  have hRc : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal (arc.take x.length))
      (GGT.RelLetter.listVal L * GGT.RelLetter.listVal arc) R := by
    intro j hj hc hv
    rw [htake] at hv
    exact (hR j hj hc (inv_mul_mem_symm hv)).elim
  have hval := hm.face.arc_val_mem lam hr1 hr hN hk hcomp hLc hRc
  rw [hget] at hval
  have hinv : h⁻¹⁻¹ ∈ boundedProducts (pullbackAtoms W D lam r) N :=
    inv_mem_boundedProducts (fun _ hy => inv_mem_pullbackAtoms hy) hval
  rw [inv_inv] at hinv
  exact ⟨h, hinv, rfl⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.inv_mul_mem_symm
#audit_axioms GroupApproximation.HullSC.CutMove.quot_arc_R
#audit_axioms GroupApproximation.HullSC.CutMove.quot_arc_tail
#audit_axioms GroupApproximation.HullSC.CutMove.quot_null
#audit_axioms GroupApproximation.HullSC.CutMove.tail_letters
#audit_axioms GroupApproximation.HullSC.CutMove.outcome_before
#audit_axioms GroupApproximation.HullSC.CutMove.mem_image_of_inner
