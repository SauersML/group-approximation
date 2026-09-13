import GroupApproximation.GGT.OsinPenetration
import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMergeRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# The value argument for a pocket with no relator cell in the one-cell branch of Lemma 9.4

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, when the source and target sides of the connector
pair lie on one relator cell `Π`.  The face `f` reads `X`, then an arc `q` of `Π` backwards, then
`Y`, then an arc `p` of `Π` backwards.  On `∂Π` the arc `p` is followed by a stretch `M`, then
`q`, then a stretch `M'`, so `X M'` and `Y M` are closed walks.  This file closes the case where
one of them bounds a pocket with no relator cell.  It uses values in `G` only, and no hypothesis
on spurs, maximality or dart minimality.

* `Embedded.listVal_dartWord_eq_inv_of_isRotated`: a closed word of value one, rotated to
  `s ++ t`, reads `t` as the inverse of `s`.
* `PocketRegion.listVal_outer_eq_one` and `PocketRegion.listVal_eq_inv_of_outer_isRotated`: the
  outer cycle of a pocket with no relator cell reads the identity, so `M'` reads `X⁻¹` (or `M`
  reads `Y⁻¹`).
* `Embedded.listVal_dartWord_eq_of_isRotated_invDarts`: the face gives `Y = q X⁻¹ p` in `G`.  So
  the arc `q M' p` of `Π` reads `Y`, and the arc `p M q` reads `X`.
* `Embedded.CyclicArc.exists_darts_eq_of_rotate_eq`: a prefix of a rotated carrier is an arc.
* `Embedded.CyclicArc.lambda_mul_length_sub_le_wordNorm`: under `C(ε, μ, λ, c, ρ)` an arc of
  length `L` of a relator cell reads an element of word norm at least `λ L - c`.
* `false_of_cellFree_pocket_X` and `false_of_cellFree_pocket_Y`: the two cases contradict
  `|Y| + c < λ (|p| + |q|)` and `|X| + c < λ (|p| + |q|)`, where `|·|` is the word norm of the
  connector's value.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

namespace Embedded

/-- **A closed word of value one, rotated to `s ++ t`, reads `t` as the inverse of `s`.** -/
theorem listVal_dartWord_eq_inv_of_isRotated (Delta : DiscDiagram.{u, w, v} W)
    {l s t : List Delta.toCombMap.Dart} (hl : GGT.RelLetter.listVal (dartWord Delta l) = 1)
    (hrot : l ~r s ++ t) :
    GGT.RelLetter.listVal (dartWord Delta t) =
      (GGT.RelLetter.listVal (dartWord Delta s))⁻¹ := by
  obtain ⟨k, hk⟩ := hrot
  have h := listVal_dartWord_rotate Delta l k
  rw [hk, hl, mul_one, inv_mul_cancel, dartWord_append, HullSC.RelWord.listVal_append] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **A face met by two arcs of one cell.**  A closed word of value one that reads `X`, then `q`
backwards, then `Y`, then `p` backwards, reads `Y` as `q X⁻¹ p`. -/
theorem listVal_dartWord_eq_of_isRotated_invDarts (Delta : DiscDiagram.{u, w, v} W)
    {l X Y p q : List Delta.toCombMap.Dart} (hl : GGT.RelLetter.listVal (dartWord Delta l) = 1)
    (hrot : l ~r X ++ invDarts Delta q ++ Y ++ invDarts Delta p) :
    GGT.RelLetter.listVal (dartWord Delta Y) =
      GGT.RelLetter.listVal (dartWord Delta q) *
        (GGT.RelLetter.listVal (dartWord Delta X))⁻¹ *
          GGT.RelLetter.listVal (dartWord Delta p) := by
  have h := listVal_dartWord_eq_inv_of_isRotated Delta hl hrot
  simp only [listVal_dartWord_invDarts, dartWord_append, HullSC.RelWord.listVal_append] at h
  rw [inv_inj.mp h]
  group

namespace CyclicArc

/-- **A prefix of a rotated carrier is an arc.** -/
theorem exists_darts_eq_of_rotate_eq {Dart : Type v} {cycle : List Dart} {m : ℕ}
    {a b : List Dart} (hrot : cycle.rotate m = a ++ b) :
    ∃ arc : CyclicArc cycle, arc.darts = a := by
  have hlength : a.length ≤ cycle.length := by
    have h := congrArg List.length hrot
    rw [List.length_rotate, List.length_append] at h
    omega
  have hstart : cycle.rotate (m % cycle.length % (cycle.length + 1)) = cycle.rotate m := by
    rcases Nat.eq_zero_or_pos cycle.length with h | h
    · rw [List.length_eq_zero_iff.mp h, List.nil_rotate, List.nil_rotate]
    · rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_lt (Nat.mod_lt m h)), List.rotate_mod]
  refine ⟨⟨⟨m % cycle.length % (cycle.length + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩, a.length,
    hlength⟩, ?_⟩
  rw [darts, rotated_eq_rotate]
  dsimp only
  rw [hstart, hrot]
  exact List.take_left' rfl

/-- **An arc of a relator cell reads a long element.**  Under `C(ε, μ, λ, c, ρ)`, an arc of
length `L` of a relator cell reads an element of word norm at least `λ L - c`. -/
theorem lambda_mul_length_sub_le_wordNorm {D : GGT.RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    (arc : CyclicArc (cellDarts Delta i)) :
    lambda * (arc.length : ℝ) - c ≤
      (WordMetric.wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal (dartWord Delta arc.darts)) : ℝ) := by
  have hq := (isLambdaCQuasiGeodesicWord_darts_cellDarts hcond arc).2 0
    (dartWord Delta arc.darts).length (Nat.zero_le _) le_rfl
  rw [GGT.OsinComponents.vertex_zero, GGT.OsinComponents.vertex_length, one_mul,
    WordMetric.wordDist_one_left, Nat.sub_zero] at hq
  have hlength : (dartWord Delta arc.darts).length = arc.length := by
    rw [dartWord, List.length_map, arc.darts_length]
  rwa [hlength] at hq

/-- **An arc of a relator cell that reads a short element is short.**  Under `C(ε, μ, λ, c, ρ)`
with `0 ≤ λ`, an arc of length at least `L` does not read an element whose word norm plus `c` is
less than `λ L`. -/
theorem false_of_wordNorm_add_lt {D : GGT.RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcond : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 ≤ lambda)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    (arc : CyclicArc (cellDarts Delta i)) {L : ℕ} (hL : L ≤ arc.length)
    (hlong : (WordMetric.wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal (dartWord Delta arc.darts)) : ℝ) + c < lambda * L) : False := by
  have hq := lambda_mul_length_sub_le_wordNorm hcond arc
  have hmul : lambda * (L : ℝ) ≤ lambda * arc.length :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hL) hlambda
  linarith

end CyclicArc

end Embedded

namespace PocketRegion

variable {Delta : DiscDiagram.{u, w, v} W}

/-- **The outer cycle of a pocket with no relator cell reads the identity.** -/
theorem listVal_outer_eq_one (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta P.outer.cycle) = 1 := by
  obtain ⟨k, hk⟩ := P.invDarts_outer_rotate
  have hrot : Embedded.invDarts Delta P.outer.cycle ~r P.inner.cycle :=
    List.IsRotated.symm ⟨k, hk.symm⟩
  have h := P.listVal_eq_one_of_isRotated hcells hrot
  rw [Embedded.listVal_dartWord_invDarts] at h
  exact inv_eq_one.mp h

/-- **Across a pocket with no relator cell, the two parts of the outer cycle read inverse
elements.** -/
theorem listVal_eq_inv_of_outer_isRotated (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) {s t : List Delta.toCombMap.Dart}
    (hrot : P.outer.cycle ~r s ++ t) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta t) =
      (GGT.RelLetter.listVal (Embedded.dartWord Delta s))⁻¹ :=
  Embedded.listVal_dartWord_eq_inv_of_isRotated Delta (P.listVal_outer_eq_one hcells) hrot

end PocketRegion

/-- **The value argument, pocket across `X`.**  A closed word `l` of value one reads `X`, then
the arc `q` backwards, then `Y`, then the arc `p` backwards.  A pocket with no relator cell has
outer cycle `X` followed by `M`, and the arc `S` of the same cell reads `q`, `M`, `p` in turn.
Then `S` reads `Y`, so `λ (|p| + |q|)` is at most the word norm of `Y` plus `c`. -/
theorem false_of_cellFree_pocket_X {D : GGT.RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 ≤ lambda)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    {l X Y M : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q S : Embedded.CyclicArc (Embedded.cellDarts Delta i))
    (hrot : l ~r X ++ Embedded.invDarts Delta q.darts ++ Y ++ Embedded.invDarts Delta p.darts)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r X ++ M) (hS : S.darts = q.darts ++ M ++ p.darts)
    (hlong : (WordMetric.wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal (Embedded.dartWord Delta Y)) : ℝ) + c <
      lambda * (p.length + q.length : ℕ)) : False := by
  have hM := P.listVal_eq_inv_of_outer_isRotated hcells hpocket
  have hface := Embedded.listVal_dartWord_eq_of_isRotated_invDarts Delta hl hrot
  have hvalue : GGT.RelLetter.listVal (Embedded.dartWord Delta S.darts) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta Y) := by
    rw [hS, Embedded.dartWord_append, HullSC.RelWord.listVal_append, Embedded.dartWord_append,
      HullSC.RelWord.listVal_append, hM, hface]
  have hlength : p.length + q.length ≤ S.length := by
    have h := congrArg List.length hS
    simp only [List.length_append, Embedded.CyclicArc.darts_length] at h
    omega
  exact Embedded.CyclicArc.false_of_wordNorm_add_lt hcond hlambda S hlength
    (by rw [hvalue]; exact hlong)

/-- **The value argument, pocket across `Y`.**  As `false_of_cellFree_pocket_X`, with the pocket
outer cycle `Y` followed by `M` and the arc `S` reading `p`, `M`, `q` in turn.  Then `S` reads
`X`. -/
theorem false_of_cellFree_pocket_Y {D : GGT.RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 ≤ lambda)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    {l X Y M : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q S : Embedded.CyclicArc (Embedded.cellDarts Delta i))
    (hrot : l ~r X ++ Embedded.invDarts Delta q.darts ++ Y ++ Embedded.invDarts Delta p.darts)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r Y ++ M) (hS : S.darts = p.darts ++ M ++ q.darts)
    (hlong : (WordMetric.wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal (Embedded.dartWord Delta X)) : ℝ) + c <
      lambda * (p.length + q.length : ℕ)) : False := by
  have hrot' :
      l ~r Y ++ Embedded.invDarts Delta p.darts ++ X ++ Embedded.invDarts Delta q.darts := by
    refine hrot.trans ?_
    simpa only [List.append_assoc] using
      (List.isRotated_append (l := X ++ Embedded.invDarts Delta q.darts)
        (l' := Y ++ Embedded.invDarts Delta p.darts))
  have hM := P.listVal_eq_inv_of_outer_isRotated hcells hpocket
  have hface := Embedded.listVal_dartWord_eq_of_isRotated_invDarts Delta hl hrot'
  have hvalue : GGT.RelLetter.listVal (Embedded.dartWord Delta S.darts) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta X) := by
    rw [hS, Embedded.dartWord_append, HullSC.RelWord.listVal_append, Embedded.dartWord_append,
      HullSC.RelWord.listVal_append, hM, hface]
  have hlength : p.length + q.length ≤ S.length := by
    have h := congrArg List.length hS
    simp only [List.length_append, Embedded.CyclicArc.darts_length] at h
    omega
  exact Embedded.CyclicArc.false_of_wordNorm_add_lt hcond hlambda S hlength
    (by rw [hvalue]; exact hlong)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.listVal_dartWord_eq_inv_of_isRotated
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.listVal_dartWord_eq_of_isRotated_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_darts_eq_of_rotate_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.lambda_mul_length_sub_le_wordNorm
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.false_of_wordNorm_add_lt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.listVal_outer_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.listVal_eq_inv_of_outer_isRotated
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_X
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_Y
