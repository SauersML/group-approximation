import GroupApproximation.GGT.HullSCLemma51LetterPullbackCutBlocks

/-!
# The lift of a certificate cut

A cut move rotates the lifted quotient-null word to `arc ++ tail`, where `arc` is the arc of a
cut face `ext = L · arc · R` (`CutFace`) of a relator `ext ++ rem ∈ W`.  The same rotation is a
rotated lift `x ++ comp λ h⁻¹ :: y` (`RotatedLift`).  The new quotient-null word is
`respellInv L ++ respellInv rem ++ respellInv R ++ tail`.

* `CutLift`: the data of one cut move.
* `CutLiftOutcome`: every cut lift has an outcome at a radius bounding the face.
* `CutLift.map_side_inv`: the respelled sides and relator rest end at the image of the arc,
  `q(L)⁻¹ · q(rem)⁻¹ · q(R)⁻¹ = q(arc)`.
* `CutLift.length_lt`, `CutLift.null_word`: the new word is shorter and quotient-null.
* `pullbackOutcome_of_blocks`: the designated outcome from the two blocks around the designated
  letter.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **A certificate cut of a rotated lift.**  The lifted word rotates to `arc ++ tail` and to
`x ++ comp λ h⁻¹ :: y`.  `arc` is the arc of the cut face `ext = L · arc · R` of the relator
`ext ++ rem`, which is null in the quotient, and `|L| + |rem| + |R| < |arc|`. -/
structure CutLift (W : Set (List (GGT.RelLetter G Lambda))) (D : GGT.RelGenSet G Lambda)
    (q : G →* Q) (hq : Function.Surjective q) (lam : Lambda) (h : G) (c : Q)
    (L arc R ext rem tail x y : List (GGT.RelLetter G Lambda)) : Prop where
  lift : RotatedLift D q hq lam h c x y
  mem : h ∈ D.fam lam
  face : CutFace W D L arc R ext
  split : arc ++ tail = x ++ GGT.RelLetter.comp lam h⁻¹ :: y
  relator : ext ++ rem ∈ W
  rem_adm : RelWord.IsAdmissible D rem
  rem_null : q (GGT.RelLetter.listVal ext * GGT.RelLetter.listVal rem) = 1
  short : L.length + rem.length + R.length < arc.length

/-- **The outcome of a certificate cut**: every cut lift has an outcome at a radius `r` bounding
the face and count `N > r`, with the new word of length at most `n` when `|x| + |y| ≤ n + 1`. -/
def CutLiftOutcome (W : Set (List (GGT.RelLetter G Lambda))) (D : GGT.RelGenSet G Lambda)
    (q : G →* Q) (hq : Function.Surjective q) : Prop :=
  ∀ {lam : Lambda} {h : G} {c : Q} {L arc R ext rem tail x y : List (GGT.RelLetter G Lambda)}
    {r N n : ℕ}, CutLift W D q hq lam h c L arc R ext rem tail x y → 1 ≤ r →
      L.length + arc.length + R.length + ext.length ≤ r → r + 1 ≤ N →
      x.length + y.length ≤ n + 1 → PullbackOutcome D q hq lam (pullbackAtoms W D lam r) N h n

section CutLift

variable {W : Set (List (GGT.RelLetter G Lambda))} {D : GGT.RelGenSet G Lambda} {q : G →* Q}
  {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
  {L arc R ext rem tail x y : List (GGT.RelLetter G Lambda)}

/-- **The respelled sides and relator rest end at the image of the arc.** -/
theorem CutLift.map_side_inv (hcl : CutLift W D q hq lam h c L arc R ext rem tail x y) :
    (q (GGT.RelLetter.listVal L))⁻¹ * (q (GGT.RelLetter.listVal rem))⁻¹ *
      (q (GGT.RelLetter.listVal R))⁻¹ = q (GGT.RelLetter.listVal arc) := by
  have hk := hcl.rem_null
  simp only [hcl.face.value, map_mul] at hk
  calc (q (GGT.RelLetter.listVal L))⁻¹ * (q (GGT.RelLetter.listVal rem))⁻¹ *
        (q (GGT.RelLetter.listVal R))⁻¹
      = (q (GGT.RelLetter.listVal L))⁻¹ *
          (q (GGT.RelLetter.listVal L) * q (GGT.RelLetter.listVal arc) *
            q (GGT.RelLetter.listVal R) * q (GGT.RelLetter.listVal rem)) *
          (q (GGT.RelLetter.listVal rem))⁻¹ * (q (GGT.RelLetter.listVal R))⁻¹ := by
        rw [hk, mul_one]
    _ = q (GGT.RelLetter.listVal arc) := by group

/-- The new word is shorter than the rotated lift. -/
theorem CutLift.length_lt (hcl : CutLift W D q hq lam h c L arc R ext rem tail x y) :
    L.length + rem.length + R.length + tail.length < x.length + y.length + 1 := by
  have e := congrArg List.length hcl.split
  simp only [List.length_append, List.length_cons] at e
  have hs := hcl.short
  omega

/-- **The new word is null in the quotient.** -/
theorem CutLift.null_word (hcl : CutLift W D q hq lam h c L arc R ext rem tail x y) :
    q (GGT.RelLetter.listVal (respellInv D L ++ respellInv D rem ++ respellInv D R ++ tail)) =
      1 := by
  have e := hcl.lift.null
  rw [← hcl.split, GGT.OsinComponents.listVal_append, map_mul] at e
  simp only [GGT.OsinComponents.listVal_append, listVal_respellInv, map_mul, map_inv]
  rw [hcl.map_side_inv]
  exact e

/-- The letters of the new word are letters of `D`. -/
theorem CutLift.isLetter_word (hcl : CutLift W D q hq lam h c L arc R ext rem tail x y) :
    ∀ a ∈ respellInv D L ++ respellInv D rem ++ respellInv D R ++ tail, D.IsLetter a := by
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · exact isLetter_respellInv D hcl.face.left_adm a ha
  · exact isLetter_respellInv D hcl.rem_adm a ha
  · exact isLetter_respellInv D hcl.face.right_adm a ha
  · have hmem : a ∈ arc ++ tail := List.mem_append_right _ ha
    rw [hcl.split] at hmem
    exact hcl.lift.letters a hmem

end CutLift

/-- **A designated outcome from two blocks.**  The word read after the designated letter `z` is
`u₂ ++ u₁`; its blocks are read at the vertex after `z` and at `1`. -/
theorem pullbackOutcome_of_blocks (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) {lam : Lambda} {A : Set G} {N n : ℕ} {h : G}
    {u₁ u₂ : List (GGT.RelLetter G Lambda)} {z : GGT.RelLetter G Lambda} {c : Q}
    (hlet : ∀ a ∈ u₁ ++ z :: u₂, D.IsLetter a)
    (hnull : q (GGT.RelLetter.listVal (u₁ ++ z :: u₂)) = 1) (hlen : (u₂ ++ u₁).length ≤ n)
    (hcomp : GGT.RelLetter.IsCompOf lam z)
    (hcos : c⁻¹ * q (GGT.RelLetter.listVal u₁) ∈ (D.mapSurjective q hq).fam lam)
    (hdes : DesignatedValue A N h z.val)
    (h2 : CosetLettersAt (D.mapSurjective q hq) lam (q '' boundedProducts A N) c
      (q (GGT.RelLetter.listVal u₁ * z.val)) (u₂.map (GGT.RelLetter.mapHom q)))
    (h1 : CosetLettersAt (D.mapSurjective q hq) lam (q '' boundedProducts A N) c 1
      (u₁.map (GGT.RelLetter.mapHom q))) :
    PullbackOutcome D q hq lam A N h n := by
  refine Or.inr ⟨u₁, u₂, z, c, hlet, hnull, hlen, hcomp, hcos, hdes, ?_⟩
  have e : q (GGT.RelLetter.listVal u₁ * z.val) * q (GGT.RelLetter.listVal u₂) = 1 := by
    simpa only [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_cons, map_mul,
      mul_assoc] using hnull
  rw [List.map_append]
  refine h2.append ?_
  rwa [GGT.RelLetter.listVal_map_mapHom, e]

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.CutLift.map_side_inv
#audit_axioms GroupApproximation.HullSC.CutLift.length_lt
#audit_axioms GroupApproximation.HullSC.CutLift.null_word
#audit_axioms GroupApproximation.HullSC.CutLift.isLetter_word
#audit_axioms GroupApproximation.HullSC.pullbackOutcome_of_blocks
