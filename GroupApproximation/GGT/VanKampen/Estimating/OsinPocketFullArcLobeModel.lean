import GroupApproximation.GGT.VanKampen.CactusBoundary
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.Meta.AxiomGuard

/-!
# A lake whose pocket holds two cells, not of least area

The first half of a model test for the component route of the transports at a full source arc
(Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b)).  Gluing an O-equivalent copy of the pocket
back into the diagram along a non-following seam can split off a component
(`OsinPocketFullArcLakeGlueModel`).  The component route removes such a component, which carries
no relator cell when the diagram has least area.  This file builds a diagram where the hypothesis
fails and a bad copy can exist, for the second half of the test.

The map is a rose with three loops at one vertex: darts `0, …, 5`, `alpha = (0 1)(2 3)(4 5)`,
`sigma : 0 ↦ 1 ↦ 4 ↦ 2 ↦ 3 ↦ 5 ↦ 0`.  Its faces are `A = [0,4]`, `Π = [1]`, `B = [2,5]` and the
exterior `O = [3]`.  Over `Perm (Fin 3)`, with `x`, `y` transpositions and `z` a 3-cycle, `Π` reads
`x⁻¹`, `A` reads `x z`, `B` reads `y z⁻¹`, and the diagram reads `y`.

* `diagram`: the disc diagram with the relator cells `Π`, `A`, `B`.
* `not_leastArea`: `y` is conjugate to `x⁻¹`, so one relator fills the boundary.
* `isNoncrossingClosedWalk_lobeWalk`: the walk `[0,2]`, the boundary of `{A, B}`, is noncrossing.
* `innerCycle_followsBoundary`: its inner cycle follows its boundary across the internal loop `{4,5}`.
* `lobePocket`: the pocket region of the walk from the Euler equalities of both reclosings; it holds
  a relator cell and fewer relator cells than the diagram.
* `lobeLake`: all of this.

## Manuscript status

Model test for infrastructure of `thm:hull` (tex 2121, "Hull's small cancellation theorem",
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OsinPocketFullArcLobeModel

open Equiv GroupApproximation.HullSC GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open Surgery.MapCollapse (BoundaryWalk InternalDart reclosedMap)

/-! ## The map -/

def lobeAlpha : Perm (Fin 6) where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide
  right_inv := by decide

def lobeSigma : Perm (Fin 6) where
  toFun := ![1, 4, 3, 5, 2, 0]
  invFun := ![5, 0, 4, 2, 1, 3]
  left_inv := by decide
  right_inv := by decide

def M : CombMap where
  Dart := Fin 6
  dartFintype := inferInstance
  alpha := lobeAlpha
  sigma := lobeSigma
  alpha_involutive := by intro d; fin_cases d <;> rfl
  alpha_fixedPointFree := by decide

instance : DecidableEq M.Dart := inferInstanceAs (DecidableEq (Fin 6))
instance (n : ℕ) : OfNat M.Dart n := inferInstanceAs (OfNat (Fin 6) n)

def faceClass : Fin 6 → Fin 4 := ![0, 1, 2, 3, 0, 2]
def faceRep : Fin 4 → Fin 6 := ![0, 1, 2, 3]

noncomputable def faceEquiv : M.Face ≃ Fin 4 :=
  OrbitClassifier.orbitEquiv M.facePerm faceClass faceRep (by decide) (by decide) (by decide)

noncomputable def vertexEquiv : M.Vertex ≃ Fin 1 :=
  OrbitClassifier.orbitEquiv M.sigma (![0, 0, 0, 0, 0, 0] : Fin 6 → Fin 1) (![0] : Fin 1 → Fin 6)
    (by decide) (by decide) (by decide)

theorem planar : M.IsPlanar := by
  constructor
  · have hstep : ∀ d : Fin 6, Relation.EqvGen M.Adjacent 0 d := by
      have h01 : Relation.EqvGen M.Adjacent 0 1 := .rel _ _ (Or.inr rfl)
      have h14 : Relation.EqvGen M.Adjacent 1 4 := .rel _ _ (Or.inr rfl)
      have h42 : Relation.EqvGen M.Adjacent 4 2 := .rel _ _ (Or.inr rfl)
      have h23 : Relation.EqvGen M.Adjacent 2 3 := .rel _ _ (Or.inr rfl)
      have h35 : Relation.EqvGen M.Adjacent 3 5 := .rel _ _ (Or.inr rfl)
      have h4 := Relation.EqvGen.trans _ _ _ h01 h14
      have h2 := Relation.EqvGen.trans _ _ _ h4 h42
      have h3 := Relation.EqvGen.trans _ _ _ h2 h23
      have h5 := Relation.EqvGen.trans _ _ _ h3 h35
      intro d
      fin_cases d
      · exact .refl _
      · exact h01
      · exact h2
      · exact h3
      · exact h4
      · exact h5
    intro d e
    exact .trans _ _ _ (.symm _ _ (hstep d)) (hstep e)
  · have hv : M.vertexCount = 1 := (Nat.card_congr vertexEquiv).trans (by simp)
    have hf : M.faceCount = 4 := (Nat.card_congr faceEquiv).trans (by simp)
    have hd : M.dartCount = 6 := by simp [CombMap.dartCount, M]
    have he := M.dartCount_eq_two_mul_edgeCount
    unfold CombMap.eulerCharacteristic
    rw [hv, hf]
    have heq : M.edgeCount = 3 := by omega
    rw [heq]
    norm_num

/-! ## The faces -/

def face (i : Fin 4) : M.Face := M.faceOf (faceRep i)

@[simp] theorem faceEquiv_face (i : Fin 4) : faceEquiv (face i) = i := by
  change faceClass (faceRep i) = i
  fin_cases i <;> rfl

theorem faceOf_eq_face (d : Fin 6) (i : Fin 4) :
    M.faceOf d = face i ↔ faceClass d = i := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face]
  rfl

theorem face_eq_iff (i j : Fin 4) : face i = face j ↔ i = j := by
  rw [← faceEquiv.injective.eq_iff, faceEquiv_face, faceEquiv_face]

def faceDarts : Fin 4 → List (Fin 6) := ![[0, 4], [1], [2, 5], [3]]

noncomputable def indexedBoundary (i : Fin 4) : FaceBoundary M (face i) where
  darts := faceDarts i
  nonempty := by change faceDarts i ≠ ([] : List (Fin 6)); fin_cases i <;> decide
  nodup := by fin_cases i <;> decide
  mem_iff := by
    intro d
    rw [faceOf_eq_face]
    fin_cases i <;> fin_cases d <;> decide
  chain := by fin_cases i <;> decide
  closes := by fin_cases i <;> decide
  length_eq_degree := by
    have h := closedOrbitList.length_eq_orbitDegree M.facePerm (faceRep i)
    have hd : closedOrbitList M.facePerm (faceRep i) = faceDarts i := by
      fin_cases i <;> decide
    rw [hd] at h
    exact h

noncomputable def boundary (f : M.Face) : FaceBoundary M f :=
  (faceEquiv.left_inv f) ▸ indexedBoundary (faceEquiv f)

@[simp] theorem boundary_face_darts (i : Fin 4) :
    (boundary (face i)).darts = faceDarts i := by
  have htransport {f g : M.Face} (h : f = g) (B : FaceBoundary M f) :
      (h ▸ B).darts = B.darts := by cases h; rfl
  unfold boundary
  rw [htransport]
  exact congrArg faceDarts (faceEquiv_face i)

/-! ## The diagram -/

abbrev G := Perm (Fin 3)

/-- A transposition. -/
def gx : G := Equiv.swap 0 1

/-- A second transposition. -/
def gy : G := Equiv.swap 1 2

/-- A 3-cycle. -/
def gz : G := Equiv.swap 0 1 * Equiv.swap 1 2

def label (d : Fin 6) : RelLetter G Empty :=
  .base ((![gx, gx⁻¹, gy, gy⁻¹, gz, gz⁻¹] : Fin 6 → G) d)

def W : Set (List (RelLetter G Empty)) :=
  {[.base gx⁻¹], [.base gx, .base gz], [.base gy, .base gz⁻¹]}

def cellP : RelatorCell M (face 3) W where
  face := face 1
  face_ne_outer := (face_eq_iff 1 3).not.mpr (by decide)
  word := [.base gx⁻¹]
  word_mem := Or.inl rfl
  conjugator := 1
  reversed := false

def cellA : RelatorCell M (face 3) W where
  face := face 0
  face_ne_outer := (face_eq_iff 0 3).not.mpr (by decide)
  word := [.base gx, .base gz]
  word_mem := Or.inr (Or.inl rfl)
  conjugator := 1
  reversed := false

def cellB : RelatorCell M (face 3) W where
  face := face 2
  face_ne_outer := (face_eq_iff 2 3).not.mpr (by decide)
  word := [.base gy, .base gz⁻¹]
  word_mem := Or.inr (Or.inr rfl)
  conjugator := gz⁻¹
  reversed := false

noncomputable def diagram : DiscDiagram W where
  toCombMap := M
  planar := planar
  label := label
  label_alpha := by
    intro d
    fin_cases d <;> exact congrArg RelLetter.base (by decide)
  outerFace := face 3
  faceBoundary := boundary
  relatorCells := [cellP, cellA, cellB]
  relatorCell_faces_nodup := by
    change [face 1, face 0, face 2].Nodup
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rw [face_eq_iff, face_eq_iff]
      decide
    · rw [List.mem_singleton]
      exact (face_eq_iff 0 2).not.mpr (by decide)
  relatorCell_word := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base gx⁻¹] = (boundary (face 1)).darts.map label
      rw [boundary_face_darts]
      rfl
    rcases List.mem_cons.mp hC with rfl | hC
    · change [RelLetter.base gx, RelLetter.base gz] = (boundary (face 0)).darts.map label
      rw [boundary_face_darts]
      rfl
    · obtain rfl := List.mem_singleton.mp hC
      change [RelLetter.base gy, RelLetter.base gz⁻¹] = (boundary (face 2)).darts.map label
      rw [boundary_face_darts]
      rfl
  inner_face := by
    intro f hf
    obtain ⟨i, rfl⟩ : ∃ i, face i = f := ⟨faceEquiv f, faceEquiv.left_inv f⟩
    fin_cases i
    · exact Or.inl ⟨cellA, by simp, rfl⟩
    · exact Or.inl ⟨cellP, by simp, rfl⟩
    · exact Or.inl ⟨cellB, by simp, rfl⟩
    · exact (hf rfl).elim
  boundary_product := by
    rw [boundary_face_darts]
    decide

instance (n : ℕ) : OfNat diagram.toCombMap.Dart n := inferInstanceAs (OfNat (Fin 6) n)
instance : DecidableEq diagram.toCombMap.Dart := inferInstanceAs (DecidableEq (Fin 6))

/-- The source cell `Π`. -/
def iP : Fin diagram.rCellCount := ⟨0, by decide⟩

/-- The cell `A`. -/
def iA : Fin diagram.rCellCount := ⟨1, by decide⟩

theorem boundaryValue_eq : diagram.boundaryValue = gy := by
  change RelLetter.listVal (RelWord.revInv ((boundary (face 3)).darts.map label)) = gy
  rw [boundary_face_darts]
  decide

/-- **The diagram is not of least area**: `y = z x⁻¹ z⁻¹`, one relator. -/
theorem not_leastArea : ¬ diagram.LeastArea := by
  intro h
  have hR : RelLetter.listVal ([.base gx⁻¹] : List (RelLetter G Empty)) ∈
      RelLetter.listVal '' W :=
    ⟨[.base gx⁻¹], Or.inl rfl, rfl⟩
  have hprod : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) 1
      diagram.boundaryValue := by
    rw [boundaryValue_eq,
      show gy = gz * RelLetter.listVal ([.base gx⁻¹] : List (RelLetter G Empty)) * gz⁻¹ by decide]
    exact .conj gz (.base hR)
  have hle := h hprod
  change 3 ≤ 1 at hle
  omega

/-! ## The walk and its sides -/

/-- The walk `[0,2]`: the boundary of `{A, B}`. -/
abbrev lobeWalk : List M.Dart := [0, 2]

theorem sigma_sq_alpha_mem : ∀ d ∈ lobeWalk, (M.sigma ^ 2) (M.alpha d) ∈ lobeWalk := by decide

theorem not_keep_sigma_alpha : ∀ d ∈ lobeWalk, ¬ walkKeep M lobeWalk (M.sigma (M.alpha d)) := by
  unfold walkKeep
  decide

/-- **The walk `[0,2]` is noncrossing.** -/
theorem isNoncrossingClosedWalk_lobeWalk : IsNoncrossingClosedWalk M lobeWalk where
  ne_nil := List.cons_ne_nil _ _
  nodup := by decide
  chain := List.isChain_cons_cons.mpr ⟨vertexEquiv.injective (by decide), List.isChain_singleton _⟩
  closes := vertexEquiv.injective (by decide)
  alpha_not_mem := by decide
  turn_mem d hd := NoncrossingClosedWalkSides.turn_mem_of_first (by norm_num)
    (sigma_sq_alpha_mem d hd) fun k hk0 hk2 => by
      obtain rfl : k = 1 := by omega
      rw [pow_one]
      exact not_keep_sigma_alpha d hd

theorem side_iff (d : M.Dart) (hd : d ∈ lobeWalk) :
    M.faceOf d ∈ sideFaces M lobeWalk ∧ M.faceOf (M.alpha d) ∉ sideFaces M lobeWalk :=
  (isNoncrossingClosedWalk_lobeWalk.isBoundaryDart_sideFaces_iff planar d).mpr hd

theorem faceOf_facePerm_eq {d e : M.Dart} (h : M.facePerm d = e) : M.faceOf e = M.faceOf d := by
  rw [← h]
  exact M.faceOf_facePerm d

theorem internal_four : InternalDart M (sideFaces M lobeWalk) 4 := by
  refine ⟨?_, ?_⟩
  · rw [faceOf_facePerm_eq (show M.facePerm 0 = 4 by decide)]
    exact (side_iff 0 (by decide)).1
  · rw [show M.alpha 4 = 5 by decide, faceOf_facePerm_eq (show M.facePerm 2 = 5 by decide)]
    exact (side_iff 2 (by decide)).1

theorem internal_five : InternalDart M (sideFaces M lobeWalk) 5 := by
  refine ⟨?_, ?_⟩
  · rw [faceOf_facePerm_eq (show M.facePerm 2 = 5 by decide)]
    exact (side_iff 2 (by decide)).1
  · rw [show M.alpha 5 = 4 by decide, faceOf_facePerm_eq (show M.facePerm 0 = 4 by decide)]
    exact (side_iff 0 (by decide)).1

theorem walk_zero_two : BoundaryWalk M (sideFaces M lobeWalk) 0 2 := by
  change Relation.ReflTransGen _ (M.facePerm 0) 2
  rw [show M.facePerm 0 = 4 by decide]
  exact Relation.ReflTransGen.single ⟨internal_four, by decide⟩

theorem walk_two_zero : BoundaryWalk M (sideFaces M lobeWalk) 2 0 := by
  change Relation.ReflTransGen _ (M.facePerm 2) 0
  rw [show M.facePerm 2 = 5 by decide]
  exact Relation.ReflTransGen.single ⟨internal_five, by decide⟩

theorem innerCycle_getLast :
    (isNoncrossingClosedWalk_lobeWalk.innerCycle planar).cycle.getLast
      (isNoncrossingClosedWalk_lobeWalk.innerCycle planar).cycle_nonempty = 2 := by
  decide

theorem innerCycle_head :
    (isNoncrossingClosedWalk_lobeWalk.innerCycle planar).cycle.head
      (isNoncrossingClosedWalk_lobeWalk.innerCycle planar).cycle_nonempty = 0 := by
  decide

/-- **The inner cycle of the walk follows its boundary**, across the internal loop `{4,5}`. -/
theorem innerCycle_followsBoundary :
    (isNoncrossingClosedWalk_lobeWalk.innerCycle planar).FollowsBoundary := by
  refine Surgery.MapCollapse.BoundaryCycle.followsBoundary_of_chain _ ?_ ?_
  · change lobeWalk.IsChain (BoundaryWalk M (sideFaces M lobeWalk))
    exact List.isChain_cons_cons.mpr ⟨walk_zero_two, List.isChain_singleton _⟩
  · rw [innerCycle_getLast, innerCycle_head]
    exact walk_two_zero

/-! ## The pocket region -/

theorem eulers :
    (reclosedMap M (sideFaces M lobeWalk)
        (isNoncrossingClosedWalk_lobeWalk.innerCycle planar)).eulerCharacteristic =
        M.eulerCharacteristic ∧
      (reclosedMap M (sideOutside M lobeWalk)
        (isNoncrossingClosedWalk_lobeWalk.outerCycle planar)).eulerCharacteristic =
        M.eulerCharacteristic :=
  isNoncrossingClosedWalk_lobeWalk.eulers_of_eitherFollows planar
    (Or.inr innerCycle_followsBoundary)

theorem outerFace_not_mem_sideFaces :
    diagram.outerFace ∉ sideFaces diagram.toCombMap lobeWalk := by
  have h := (side_iff 2 (by decide)).2
  rw [show M.alpha 2 = 3 by decide] at h
  exact h

theorem source_not_mem_sideFaces :
    (Embedded.cell diagram iP).face ∉ sideFaces diagram.toCombMap lobeWalk := by
  have h := (side_iff 0 (by decide)).2
  rw [show M.alpha 0 = 1 by decide] at h
  exact h

theorem cellA_mem_sideFaces :
    (Embedded.cell diagram iA).face ∈ sideFaces diagram.toCombMap lobeWalk :=
  (side_iff 0 (by decide)).1

/-- **The pocket region of the walk**, holding `A` and `B`. -/
noncomputable def lobePocket : PocketRegion diagram :=
  PocketRegion.ofNoncrossingClosedWalkEuler isNoncrossingClosedWalk_lobeWalk
    outerFace_not_mem_sideFaces eulers.1 eulers.2

theorem lobePocket_invDarts_outer :
    Embedded.invDarts diagram lobePocket.outer.cycle = lobeWalk := by
  change Embedded.invDarts diagram (lobeWalk.reverse.map diagram.toCombMap.alpha) = lobeWalk
  exact PocketRegion.invDarts_reverse_map_alpha (Delta := diagram) lobeWalk

theorem lobePocket_rCellCount_pos : 0 < lobePocket.diagram.rCellCount :=
  lobePocket.diagram_rCellCount_pos (Embedded.cell_mem diagram iA) cellA_mem_sideFaces

theorem lobePocket_rCellCount_lt : lobePocket.diagram.rCellCount < diagram.rCellCount :=
  lobePocket.diagram_rCellCount_lt (Embedded.cell_mem diagram iP) source_not_mem_sideFaces

/-! ## The endpoint -/

/-- **A lake whose pocket holds two cells** (model test, first half).  The diagram is not of least
area, the walk `[0,2]` is noncrossing with its inner cycle following, and the pocket region of the
walk from the Euler equalities holds a relator cell and fewer relator cells than the diagram. -/
def LobeLakeStatement : Prop :=
  ¬ diagram.LeastArea ∧ IsNoncrossingClosedWalk diagram.toCombMap lobeWalk ∧
    (isNoncrossingClosedWalk_lobeWalk.innerCycle planar).FollowsBoundary ∧
    ∃ P : PocketRegion diagram, P.faces = sideFaces diagram.toCombMap lobeWalk ∧
      Embedded.invDarts diagram P.outer.cycle = lobeWalk ∧ 0 < P.diagram.rCellCount ∧
      P.diagram.rCellCount < diagram.rCellCount

theorem lobeLake : LobeLakeStatement :=
  ⟨not_leastArea, isNoncrossingClosedWalk_lobeWalk, innerCycle_followsBoundary, lobePocket, rfl,
    lobePocket_invDarts_outer, lobePocket_rCellCount_pos, lobePocket_rCellCount_lt⟩

end GroupApproximation.GGT.VanKampen.OsinPocketFullArcLobeModel

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketFullArcLobeModel.not_leastArea
#audit_axioms GroupApproximation.GGT.VanKampen.OsinPocketFullArcLobeModel.innerCycle_followsBoundary
#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketFullArcLobeModel.lobeLake
