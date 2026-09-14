import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactMap
import GroupApproximation.GGT.VanKampen.CombMapBipartiteSmallFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the degenerate small faces of the contact map

`OsinLemma94ContactMapSmallFacesInput` (`OsinLemma94ContactMap.lean`) bounds the faces of degree
less than six of `contactMap P`.  Every face has degree at least four, so these are faces of degree
four, read from a representative `x` as `x, φx, φ²x, φ³x`.

* A face is **degenerate** when `x` and `φ²x` start at one polygon.  Then the rotation fixes the
  object dart `φx`, a pendant object (`CombMap.card_filter_degenerate_le`).  Such darts inject into
  the objects (`card_fixed_colour_false_le`): each lies at the face of its object, the vertex of the
  contact map is determined by that face (`vertexOf_eq_of_faceOf_eq`), and a fixed dart is alone at
  its vertex.  So there are at most `n + 1` degenerate faces.
* A **nondegenerate** face reads two distinct rich polygons and, by
  `CombMap.vertexOf_facePerm_ne_pow_three`, two distinct objects: a two-gon `(f, a, f′, b)`.
  `OsinLemma94ContactMapNondegenerateSmallFacesInput` bounds these.  It either holds a relator
  cell, or it is an empty two-gon excluded by the region merge.

`osinLemma94ContactMapSmallFacesInput_of_nondegenerate`: the small faces from the nondegenerate
ones, with constant `K + 2`.  **This is a reduction: the nondegenerate count is open.**

Model tests (hand).
* The contact map `a – f – b` with both objects pendant: one degenerate face of degree four,
  charged to `a`; `n + 1 ≥ 1`.
* Two rich polygons around cells `a` and `b` (a square): two nondegenerate faces, both counted by
  the residual.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- An object dart of the contact map lies at the face of its object. -/
theorem exists_faceOf_eq_objectFace (P : OsinLemma94RealizedPolygons S) (y : P.contactMap.Dart)
    (hy : P.contactColour y = false) :
    ∃ o, S.diagram.toCombMap.faceOf y.1 = objectFace S o := by
  rcases P.isRep_or y with h | ⟨k, o, h, -, hx⟩
  · exact absurd ((P.contactColour_eq_true_iff y).mpr h) (by rw [hy]; simp)
  · refine ⟨o, ?_⟩
    have e := P.faceOf_alpha_rep k o h
    rw [← hx, S.diagram.toCombMap.alpha_involutive] at e
    exact e

/-- Two darts of the contact map based at one face of the diagram lie at one vertex. -/
theorem vertexOf_eq_of_faceOf_eq (P : OsinLemma94RealizedPolygons S) {x y : P.contactMap.Dart}
    (h : S.diagram.toCombMap.faceOf x.1 = S.diagram.toCombMap.faceOf y.1) :
    P.contactMap.vertexOf x = P.contactMap.vertexOf y := by
  rw [P.contactMap_isRestriction.vertexOf_eq_iff x y, CombMap.vertexOf_eq_iff]
  exact (S.diagram.toCombMap.faceOf_eq_iff _ _).mp h

/-- **The pendant object darts number at most `n + 1`.** -/
theorem card_fixed_colour_false_le (P : OsinLemma94RealizedPolygons S) :
    (Finset.univ.filter fun y : P.contactMap.Dart =>
        P.contactColour y = false ∧ P.contactMap.sigma y = y).card ≤
      S.diagram.rCellCount + 1 := by
  let g : P.contactMap.Dart → Option (Fin S.diagram.rCellCount) := fun y =>
    if h : ∃ o, S.diagram.toCombMap.faceOf y.1 = objectFace S o then Classical.choose h else none
  have hg : ∀ y, P.contactColour y = false →
      S.diagram.toCombMap.faceOf y.1 = objectFace S (g y) := by
    intro y hy
    have h := P.exists_faceOf_eq_objectFace y hy
    have hgy : g y = Classical.choose h := dif_pos h
    rw [hgy]
    exact Classical.choose_spec h
  refine (Finset.card_le_card_of_injOn g
    (fun y _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_).trans ?_
  · intro y hy y' hy' hyy'
    obtain ⟨hyc, hyf⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    obtain ⟨hyc', -⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hy')).2
    have hface : S.diagram.toCombMap.faceOf y.1 = S.diagram.toCombMap.faceOf y'.1 :=
      (hg y hyc).trans ((congrArg (objectFace S) hyy').trans (hg y' hyc').symm)
    obtain ⟨i, hi⟩ := (P.contactMap.vertexOf_eq_iff y y').mp (P.vertexOf_eq_of_faceOf_eq hface)
    rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hyf i] at hi
    exact hi
  · simp [Finset.card_univ, Fintype.card_option]

/-- **The degenerate small faces number at most `n + 1`.** -/
theorem card_degenerateFaces_le (P : OsinLemma94RealizedPolygons S) :
    (Finset.univ.filter fun F : P.contactMap.Face => ∃ x, P.contactMap.faceOf x = F ∧
        P.contactColour x = true ∧
          P.contactMap.vertexOf x =
            P.contactMap.vertexOf (P.contactMap.facePerm (P.contactMap.facePerm x))).card ≤
      S.diagram.rCellCount + 1 :=
  (CombMap.card_filter_degenerate_le P.contactMap P.contactColour P.contactColour_alpha
    P.contactColour_sigma P.contactMap_simple).trans P.card_fixed_colour_false_le

end OsinLemma94RealizedPolygons

/-- **The nondegenerate small faces of the contact map** (open).  Under the binders of
`OsinLemma94LongTransitionInput`, the faces of degree less than six of `contactMap P` whose
representatives `x` and `φ²x` start at different polygons number at most `K n`.  Such a face reads
two distinct rich polygons and two distinct objects, `(f, a, f′, b)`.

Model tests (hand).
* Two rich polygons running along cells `a` and `b`, with a third relator cell between them: one
  such face holds that cell, so at most `n` of them.
* The same two polygons with only `G`-faces and selected regions between them: an empty two-gon.
  When each polygon has one arc on `a`, one arc on `b` and one short side between the arcs, along one
  selected region, merging the two polygons with that region gives a contiguity region from `a` to
  `b`.  Its sides are the other short sides, and it is heavier, so the configuration does not occur.
  Several short sides in a row, or `d_f ≥ 3`, need a merge through sectors of the polygon faces. -/
def OsinLemma94ContactMapNondegenerateSmallFacesInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    (Finset.univ.filter fun F : P.contactMap.Face =>
                      P.contactMap.faceDegree F < 6 ∧
                        ∀ x, P.contactMap.faceOf x = F → P.contactColour x = true →
                          P.contactMap.vertexOf x ≠
                            P.contactMap.vertexOf
                              (P.contactMap.facePerm (P.contactMap.facePerm x))).card ≤
                      K * Delta.rCellCount

/-- **The small faces from the nondegenerate ones**, with constant `K + 2`. -/
theorem osinLemma94ContactMapSmallFacesInput_of_nondegenerate
    (h : OsinLemma94ContactMapNondegenerateSmallFacesInput.{u, w, v}) :
    OsinLemma94ContactMapSmallFacesInput.{u, w, v} := by
  intro _ _ _ D hhyper lambda c mu h1 h2 h3 h4 h5
  obtain ⟨e1, he⟩ := h D hhyper lambda c mu h1 h2 h3 h4 h5
  refine ⟨e1, fun eps heps => ?_⟩
  obtain ⟨K, r, hr, hK⟩ := he eps heps
  refine ⟨K + 2, r, hr,
    fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax => ?_⟩
  have hnd := hK rho hrho W hW Delta cuts hleast hcells hbelow S hcard hminimal P hmax
  have hdeg := P.card_degenerateFaces_le
  have hsplit : (Finset.univ.filter fun F : P.contactMap.Face =>
      P.contactMap.faceDegree F < 6) ⊆
      (Finset.univ.filter fun F : P.contactMap.Face => ∃ x, P.contactMap.faceOf x = F ∧
        P.contactColour x = true ∧
          P.contactMap.vertexOf x =
            P.contactMap.vertexOf (P.contactMap.facePerm (P.contactMap.facePerm x))) ∪
      (Finset.univ.filter fun F : P.contactMap.Face =>
        P.contactMap.faceDegree F < 6 ∧
          ∀ x, P.contactMap.faceOf x = F → P.contactColour x = true →
            P.contactMap.vertexOf x ≠
              P.contactMap.vertexOf (P.contactMap.facePerm (P.contactMap.facePerm x))) := by
    intro F hF
    have hsmall := (Finset.mem_filter.mp hF).2
    by_cases hd : ∃ x, P.contactMap.faceOf x = F ∧ P.contactColour x = true ∧
        P.contactMap.vertexOf x =
          P.contactMap.vertexOf (P.contactMap.facePerm (P.contactMap.facePerm x))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsmall, ?_⟩)
      intro x hx hcol hv
      exact hd ⟨x, hx, hcol, hv⟩
  have hn : S.diagram.rCellCount = Delta.rCellCount := S.equiv.rCellCount_eq
  have hunion := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have hmul : (K + 2) * Delta.rCellCount = K * Delta.rCellCount + 2 * Delta.rCellCount := by ring
  omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_fixed_colour_false_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.card_degenerateFaces_le
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ContactMapSmallFacesInput_of_nondegenerate
