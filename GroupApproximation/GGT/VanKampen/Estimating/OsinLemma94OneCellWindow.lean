import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellMorse
import GroupApproximation.Meta.AxiomGuard

/-!
# The one-cell Morse kill through windows of the face walk

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, when the source and target sides of the connector
pair lie on one relator cell `Π`.  The kills of `OsinLemma94OneCellMorse` ask the face walk to read
the arcs `p` and `q` of `Π` backwards, dart by dart.  They use this only through values.  Here the
face walk reads windows `p'` and `q'` whose values are the inverses of the values of `p` and `q`.
A window through a pinch vertex of `Π` skips the loop of `∂Π` there.  That loop reads the identity,
so the window and the arc of `Π` through the loop still read inverse elements.

* `Embedded.listVal_dartWord_eq_of_isRotated_windows`: a closed word of value one that reads `X`,
  `q'`, `Y` and `p'` in turn reads `Y` as `q X⁻¹ p`.
* `listVal_dartWord_eq_of_cellFree_pocket_windows_X` and `_Y`: the arc `q M p` (or `p M q`) of the
  cell reads `Y` (or `X`).
* `false_of_cellFree_pocket_windows_X_morse` and `_Y_morse`: the two pockets with no relator cell
  are impossible at the threshold `2κ + c ≤ λ ε`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

namespace Embedded

/-- **A face met by two windows.**  A closed word of value one that reads `X`, then `q'`, then `Y`,
then `p'`, where `q'` and `p'` read the inverses of `q` and `p`, reads `Y` as `q X⁻¹ p`. -/
theorem listVal_dartWord_eq_of_isRotated_windows (Delta : DiscDiagram.{u, w, v} W)
    {l X Y p q p' q' : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (dartWord Delta l) = 1) (hrot : l ~r X ++ q' ++ Y ++ p')
    (hq' : GGT.RelLetter.listVal (dartWord Delta q') =
      (GGT.RelLetter.listVal (dartWord Delta q))⁻¹)
    (hp' : GGT.RelLetter.listVal (dartWord Delta p') =
      (GGT.RelLetter.listVal (dartWord Delta p))⁻¹) :
    GGT.RelLetter.listVal (dartWord Delta Y) =
      GGT.RelLetter.listVal (dartWord Delta q) *
        (GGT.RelLetter.listVal (dartWord Delta X))⁻¹ *
          GGT.RelLetter.listVal (dartWord Delta p) := by
  have h := listVal_dartWord_eq_inv_of_isRotated Delta hl hrot
  simp only [dartWord_append, HullSC.RelWord.listVal_append, hq', hp'] at h
  rw [inv_inj.mp h]
  group

end Embedded

/-- **The value step through windows, pocket across `X`.**  The arc `q M p` reads `Y`. -/
theorem listVal_dartWord_eq_of_cellFree_pocket_windows_X {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount} {l X Y M p' q' : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q : Embedded.CyclicArc (Embedded.cellDarts Delta i)) (hrot : l ~r X ++ q' ++ Y ++ p')
    (hq' : GGT.RelLetter.listVal (Embedded.dartWord Delta q') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))⁻¹)
    (hp' : GGT.RelLetter.listVal (Embedded.dartWord Delta p') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts))⁻¹)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r X ++ M) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta (q.darts ++ M ++ p.darts)) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta Y) := by
  have hM := P.listVal_eq_inv_of_outer_isRotated hcells hpocket
  have hface := Embedded.listVal_dartWord_eq_of_isRotated_windows Delta hl hrot hq' hp'
  rw [Embedded.dartWord_append, HullSC.RelWord.listVal_append, Embedded.dartWord_append,
    HullSC.RelWord.listVal_append, hM, hface]

/-- **The value step through windows, pocket across `Y`.**  The arc `p M q` reads `X`. -/
theorem listVal_dartWord_eq_of_cellFree_pocket_windows_Y {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount} {l X Y M p' q' : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q : Embedded.CyclicArc (Embedded.cellDarts Delta i)) (hrot : l ~r X ++ q' ++ Y ++ p')
    (hq' : GGT.RelLetter.listVal (Embedded.dartWord Delta q') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))⁻¹)
    (hp' : GGT.RelLetter.listVal (Embedded.dartWord Delta p') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts))⁻¹)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r Y ++ M) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta (p.darts ++ M ++ q.darts)) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta X) := by
  have hrot' : l ~r Y ++ p' ++ X ++ q' := by
    refine hrot.trans ?_
    simpa only [List.append_assoc] using
      (List.isRotated_append (l := X ++ q') (l' := Y ++ p'))
  have hM := P.listVal_eq_inv_of_outer_isRotated hcells hpocket
  have hface := Embedded.listVal_dartWord_eq_of_isRotated_windows Delta hl hrot' hp' hq'
  rw [Embedded.dartWord_append, HullSC.RelWord.listVal_append, Embedded.dartWord_append,
    HullSC.RelWord.listVal_append, hM, hface]

/-- **The Morse kill through windows, pocket across `X`.**  As `false_of_cellFree_pocket_X_morse`,
with the face walk reading windows `q'` and `p'` that read the inverses of the arcs `q` and `p`. -/
theorem false_of_cellFree_pocket_windows_X_morse {D : GGT.RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 ≤ lambda) (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    {l X Y M p' q' : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q S : Embedded.CyclicArc (Embedded.cellDarts Delta i)) (hrot : l ~r X ++ q' ++ Y ++ p')
    (hq' : GGT.RelLetter.listVal (Embedded.dartWord Delta q') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))⁻¹)
    (hp' : GGT.RelLetter.listVal (Embedded.dartWord Delta p') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts))⁻¹)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r X ++ M) (hS : S.darts = q.darts ++ M ++ p.darts)
    (hY : WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta Y)) < eps)
    (hp : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts)))
    (hq : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))) : False := by
  have hword := Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts hcond S
  rw [hS, Embedded.dartWord_append, Embedded.dartWord_append] at hword
  have hvalue :=
    listVal_dartWord_eq_of_cellFree_pocket_windows_X hl p q hrot hq' hp' P hcells hpocket
  rw [Embedded.dartWord_append, Embedded.dartWord_append] at hvalue
  have hbound := hword.lambda_eps_lt_of_hairpin hmorse hlambda
    (by rw [hvalue]; exact hY) hq hp
  linarith

/-- **The Morse kill through windows, pocket across `Y`.**  As `false_of_cellFree_pocket_Y_morse`,
with the face walk reading windows `q'` and `p'` that read the inverses of the arcs `q` and `p`. -/
theorem false_of_cellFree_pocket_windows_Y_morse {D : GGT.RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 ≤ lambda) (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    {l X Y M p' q' : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q S : Embedded.CyclicArc (Embedded.cellDarts Delta i)) (hrot : l ~r X ++ q' ++ Y ++ p')
    (hq' : GGT.RelLetter.listVal (Embedded.dartWord Delta q') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))⁻¹)
    (hp' : GGT.RelLetter.listVal (Embedded.dartWord Delta p') =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts))⁻¹)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r Y ++ M) (hS : S.darts = p.darts ++ M ++ q.darts)
    (hX : WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta X)) < eps)
    (hp : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts)))
    (hq : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))) : False := by
  have hword := Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts hcond S
  rw [hS, Embedded.dartWord_append, Embedded.dartWord_append] at hword
  have hvalue :=
    listVal_dartWord_eq_of_cellFree_pocket_windows_Y hl p q hrot hq' hp' P hcells hpocket
  rw [Embedded.dartWord_append, Embedded.dartWord_append] at hvalue
  have hbound := hword.lambda_eps_lt_of_hairpin hmorse hlambda
    (by rw [hvalue]; exact hX) hp hq
  linarith

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.listVal_dartWord_eq_of_isRotated_windows
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_eq_of_cellFree_pocket_windows_X
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_eq_of_cellFree_pocket_windows_Y
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_windows_X_morse
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_windows_Y_morse
