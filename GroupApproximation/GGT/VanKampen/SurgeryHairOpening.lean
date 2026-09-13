import GroupApproximation.GGT.VanKampen.SurgeryOuterSpurThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# Opening a hair into a two-gon

A hair is an edge with one face on both sides.  A hair of the exterior is an outer spur, which
`OuterSpurThickening.sectionFamily` thickens.  A hair of an inner face `f` is doubled by
`FaceEdgeDoubling.diagram`: the digon `none, w_j` is a G-face of value one
(`FaceEdgeDoubling.boundary_digon`, `boundary_digon_value`), the rest of `f` reads the old
word with the new dart in the place of `w_j`, and every other face keeps its darts.  The new
diagram is O-equivalent over the same cuts.

If no selected region contains `f`, then no region contains the face across the hair either,
since that face is `f` again.  So every region transports with its face set, weight, target
profile and source cell (`FaceEdgeDoubling.regionFamily`).  The competitors of the new family
are the section families over diagrams O-equivalent to `Δ`, as before, so the transported family
is again globally distinguished.

* `HairOpening.regionFamilyEquiv`: the old regions correspond to the transported ones, with the
  same target profile and source cell.
* `HairOpening.sectionFamily`: a distinguished family across the doubling of an edge of an inner
  face `f`, when no region of the family contains `f` or the face across the doubled dart.
* `HairOpening.IsHair`, `one_lt_length_of_isHair`, `exists_dart_eq`.
* `HairOpening.exists_opened`: for a hair of an inner face that no region contains, there is a
  distinguished family over an O-equivalent diagram with a G-face two-gon of value one, the same
  weight, and regions in bijection with the old ones with the same target profiles and source
  cells.

The opened diagram has two more darts, so the opened family is never `DartMinimal` when the old
one is.

## Manuscript status

Infrastructure for Osin's Lemma 9.4 (arXiv:math/0411039v3, §9).  It certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.HairOpening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Regions

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The old regions correspond to the transported ones. -/
noncomputable def regionFamilyEquiv (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (j : Fin (Delta.faceBoundary f).darts.length)
    (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)
    {D : RelGenSet G Lambda} {eps : ℕ} (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1) :
    family ≃ FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid :=
  Equiv.ofBijective
    (fun a => ⟨FaceEdgeDoubling.regionFamilyEmbedding Delta f j hlen hf family havoid a,
      Finset.mem_map_of_mem _ (Finset.mem_attach family a)⟩)
    (And.intro
      (fun _ _ h => (FaceEdgeDoubling.regionFamilyEmbedding Delta f j hlen hf family havoid).injective
        (congrArg Subtype.val h))
      (fun x => by
        obtain ⟨a, _, ha⟩ := Finset.mem_map.mp x.property
        exact ⟨a, Subtype.ext ha⟩))

theorem regionFamilyEquiv_profile (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (j : Fin (Delta.faceBoundary f).darts.length)
    (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)
    {D : RelGenSet G Lambda} {eps : ℕ} (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (a : family) :
    RegionCandidate.SameTargetProfile
      (regionFamilyEquiv Delta f j hlen hf family havoid a).1 a.1 :=
  FaceEdgeDoubling.regionCandidate_profile Delta f j hlen hf ⟨a.val, havoid a.val a.property⟩

theorem regionFamilyEquiv_source (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (j : Fin (Delta.faceBoundary f).darts.length)
    (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)
    {D : RelGenSet G Lambda} {eps : ℕ} (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (a : family) :
    (regionFamilyEquiv Delta f j hlen hf family havoid a).1.2.source.val = a.1.2.source.val :=
  rfl

/-- A hair: an edge with the same face on both sides. -/
def IsHair (Delta : DiscDiagram.{u, w, v} W) (x : Delta.toCombMap.Dart) : Prop :=
  Delta.toCombMap.faceOf x = Delta.toCombMap.faceOf (Delta.toCombMap.alpha x)

theorem one_lt_length_of_isHair {Delta : DiscDiagram.{u, w, v} W} {x : Delta.toCombMap.Dart}
    (hx : IsHair Delta x) :
    1 < (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts.length := by
  have hx' : Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) = Delta.toCombMap.faceOf x :=
    Eq.symm hx
  have h1 := ((Delta.faceBoundary (Delta.toCombMap.faceOf x)).mem_iff x).mpr rfl
  have h2 := ((Delta.faceBoundary (Delta.toCombMap.faceOf x)).mem_iff _).mpr hx'
  generalize (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts = l at h1 h2 ⊢
  rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩
  · exact absurd h1 List.not_mem_nil
  · rw [List.mem_singleton] at h1 h2
    exact absurd (h2.trans h1.symm) (Delta.toCombMap.alpha_fixedPointFree x)
  · exact Nat.succ_lt_succ (Nat.succ_pos _)

/-- Every dart of a face is the doubled dart at some index of its traversal. -/
theorem exists_dart_eq {Delta : DiscDiagram.{u, w, v} W} (x : Delta.toCombMap.Dart) :
    ∃ j : Fin (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts.length,
      FaceEdgeDoubling.dart Delta (Delta.toCombMap.faceOf x) j = x := by
  obtain ⟨j, hj⟩ := List.get_of_mem
    (((Delta.faceBoundary (Delta.toCombMap.faceOf x)).mem_iff x).mpr rfl)
  exact ⟨j, by rw [FaceEdgeDoubling.dart_eq_get, hj]⟩

end Regions

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A distinguished section family across the doubling of an edge of an inner face.**  The
weight and the number of regions are unchanged and the labels stay legal, so the transported
family is again optimal. -/
noncomputable def sectionFamily (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  diagram := FaceEdgeDoubling.diagram S.diagram f j hlen hf
  equiv := S.equiv.trans (FaceEdgeDoubling.oEquivalent S.diagram f j hlen hf)
  reduced := FaceEdgeDoubling.reduced S.diagram f j hlen hf S.reduced
  family := FaceEdgeDoubling.regionFamily S.diagram f j hlen hf S.family havoid
  pairwise := FaceEdgeDoubling.regionFamily_pairwise S.diagram f j hlen hf S.family havoid
    S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      FaceEdgeDoubling.regionFamily_profile S.diagram f j hlen hf S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab
      (FaceEdgeDoubling.regionFamily_noLoop S.diagram f j hlen hf S.family havoid
        (fun x hx => (S.respects x hx).1) ha)
      (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ :=
      FaceEdgeDoubling.regionFamily_profile S.diagram f j hlen hf S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  label_admissible := FaceEdgeDoubling.label_admissible S.diagram f j hlen hf
    (symmetricLabelAlphabet D) (symmetricLabelAlphabet.symmetric D) S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (FaceEdgeDoubling.regionFamily_weight S.diagram f j hlen hf S.family havoid).symm
  card_minimal other hother hweight :=
    (FaceEdgeDoubling.regionFamily_card S.diagram f j hlen hf S.family havoid).trans_le
      (S.card_minimal other hother (hweight.trans
        (FaceEdgeDoubling.regionFamily_weight S.diagram f j hlen hf S.family havoid)))

theorem sectionFamily_diagram (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    (sectionFamily S f j hlen hf havoid).diagram = FaceEdgeDoubling.diagram S.diagram f j hlen hf :=
  rfl

theorem sectionFamily_family (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    (sectionFamily S f j hlen hf havoid).family =
      FaceEdgeDoubling.regionFamily S.diagram f j hlen hf S.family havoid :=
  rfl

/-- **Opening a hair of an inner face.**  If no region of `S` contains the face of the hair,
the hair becomes a side of a G-face two-gon of value one in an O-equivalent diagram carrying a
distinguished family with the same weight, and with regions in bijection with the old ones with
the same target profiles and source cells. -/
theorem exists_opened (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {x : S.diagram.toCombMap.Dart} (hx : IsHair S.diagram x)
    (hf : S.diagram.toCombMap.faceOf x ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf x ∉ a.1) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
          (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
            (e a).1.2.source.val = a.1.2.source.val) ∧
          ∃ g : S'.diagram.toCombMap.Face, g ≠ S'.diagram.outerFace ∧
            (S'.diagram.faceBoundary g).darts.length = 2 ∧
            RelLetter.listVal ((S'.diagram.faceBoundary g).darts.map S'.diagram.label) = 1 := by
  have hx' : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) =
      S.diagram.toCombMap.faceOf x := Eq.symm hx
  have hlen := one_lt_length_of_isHair hx
  obtain ⟨j, hj⟩ := exists_dart_eq x
  have havoid' : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf x ∉ a.1 ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j)) ∉ a.1 := by
    intro a ha
    refine ⟨havoid a ha, ?_⟩
    rw [hj, hx']
    exact havoid a ha
  refine ⟨sectionFamily S _ j hlen hf havoid',
    regionFamilyEquiv S.diagram _ j hlen hf S.family havoid',
    ⟨FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf⟩,
    FaceEdgeDoubling.regionFamily_weight S.diagram _ j hlen hf S.family havoid',
    fun a => And.intro (regionFamilyEquiv_profile S.diagram _ j hlen hf S.family havoid' a)
      (regionFamilyEquiv_source S.diagram _ j hlen hf S.family havoid' a),
    FaceEdgeDoubling.digon S.diagram _ j hlen, ?_, ?_, ?_⟩
  · intro h
    exact FaceEdgeDoubling.keep_ne_digon S.diagram _ j hlen (Ne.symm hf) h.symm
  · change (FaceEdgeDoubling.boundary S.diagram _ j hlen
      (FaceEdgeDoubling.digon S.diagram _ j hlen)).darts.length = 2
    rw [FaceEdgeDoubling.boundary_digon]
    rfl
  · exact FaceEdgeDoubling.boundary_digon_value S.diagram _ j hlen

end Family

end GroupApproximation.GGT.VanKampen.HairOpening

#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.regionFamilyEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.regionFamilyEquiv_profile
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.one_lt_length_of_isHair
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.sectionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.exists_opened
