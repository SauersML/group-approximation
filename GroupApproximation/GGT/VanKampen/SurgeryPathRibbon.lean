import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling a path into a ribbon of G-digons

Step 2 of the plan for the Greendlinger residual
`GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`: cut the diagram along a minimal path
`p` from the boundary to a nearest relator cell.  Osin (arXiv:math/0411039v3, §9) passes to an
O-equivalent diagram in which `p` is doubled, so that the two copies of `p` bound a thin region
of G-cells (a "ribbon").  This module builds that diagram one dart of `p` at a time, each doubled
inside its own face: by `FaceEdgeDoubling` when the face has at least two darts, and by
`MonogonDoubling` when it is a monogon.

* `IsRibbonAt X ι x`: the face of `x` is a G-digon with face cycle `[x, c]`.  It is inner and
  carries no relator cell, the other side `c` reads the inverse letter, and `c` is new, i.e. not
  in the range of `ι`.
* `stepEdge`, `stepMono`, `step`: one doubling.  It keeps reducedness and creates a ribbon cell at
  the doubled dart.  It transports the faces of the other darts, their membership in the face
  set, and every ribbon cell whose face is not the doubled face.
* `exists_pathRibbon`: a list `p` of distinct darts, each on an inner face, can be doubled
  completely.  There is a collar transport (`GeodesicCollar.Transport`) from the faces of `p`, i.e.
  an O-equivalence with a dart embedding compatible with `alpha` and the labels.  It keeps the
  outer boundary and the relator cells off the faces of `p`, preserves reducedness, and every
  image of a dart of `p` spans a ribbon cell.

The sides of the slit are the images of `p` and the new copies.  Assembling the pocket from them is
step 3 of the plan and is not done here.

## Manuscript status

Infrastructure for `thm:hull` (non-MF tex, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PathRibbon

open HullSC EdgeInsertion Surgery
open scoped Classical

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A ribbon cell at `x`.**  The face of `x` is a G-digon: its face cycle is `[x, c]`, it is an
inner face, and no relator cell sits on it.  The other side `c` reads the inverse letter of `x`,
and it is new: no point of `β` maps to it under `ι`. -/
@[reducible] def IsRibbonAt (X : DiscDiagram.{u, w, v} W) {β : Type v}
    (ι : β → X.toCombMap.Dart) (x : X.toCombMap.Dart) : Prop :=
  ∃ c : X.toCombMap.Dart, X.toCombMap.IsFaceCycle [x, c] ∧ (∀ a, ι a ≠ c) ∧
    X.toCombMap.faceOf x ≠ X.outerFace ∧
    (∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf x) ∧
    X.label c = RelWord.inv (X.label x)

/-- A ribbon cell survives a change of the old-dart map, as long as every newly named dart
was already named. -/
theorem IsRibbonAt.congr {X : DiscDiagram.{u, w, v} W} {β γ : Type v}
    {ι : β → X.toCombMap.Dart} {ι' : γ → X.toCombMap.Dart} {x x' : X.toCombMap.Dart}
    (h : IsRibbonAt X ι x) (hx : x' = x) (hι : ∀ a, ∃ b, ι' a = ι b) :
    IsRibbonAt X ι' x' := by
  subst hx
  obtain ⟨c, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨c, h₁, fun a hac => ?_, h₃, h₄, h₅⟩
  obtain ⟨b, hb⟩ := hι a
  exact h₂ b (hb.symm.trans hac)

/-- **The face of a ribbon cell** consists of `x` and its other side. -/
theorem IsRibbonAt.exists_faceOf_eq_iff {X : DiscDiagram.{u, w, v} W} {β : Type v}
    {ι : β → X.toCombMap.Dart} {x : X.toCombMap.Dart} (h : IsRibbonAt X ι x) :
    ∃ c, (∀ a, ι a ≠ c) ∧
      ∀ y, X.toCombMap.faceOf y = X.toCombMap.faceOf x ↔ y = x ∨ y = c := by
  obtain ⟨c, hcyc, hnew, -⟩ := h
  refine ⟨c, hnew, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · have hmem : y ∈ [x, c] := (hcyc.mem_iff y).mpr hy
    simpa using hmem
  · rintro (h | h)
    · rw [h]
    · rw [h]
      exact (hcyc.mem_iff c).mp (by simp)

/-- The conclusion of one doubling step, for the dart `d` of `X` and the face set `S`. -/
@[reducible] def StepOutput (D : RelGenSet G Lambda) (X : DiscDiagram.{u, w, v} W)
    (S : Finset X.toCombMap.Face) (d : X.toCombMap.Dart) : Prop :=
  ∃ (X' : DiscDiagram.{u, w, v} W) (S' : Finset X'.toCombMap.Face)
    (T : GeodesicCollar.Transport D S X' S'),
    (X.Reduced → X'.Reduced) ∧
    IsRibbonAt X' (fun y => T.embedding y) (T.embedding d) ∧
    ∀ x, x ≠ d →
      (X'.toCombMap.faceOf (T.embedding x) ∈ S' ↔ X.toCombMap.faceOf x ∈ S) ∧
      (X'.toCombMap.faceOf (T.embedding x) ≠ X'.outerFace ↔
        X.toCombMap.faceOf x ≠ X.outerFace) ∧
      ∀ {β : Type v} (ι : β → X.toCombMap.Dart),
        X.toCombMap.faceOf x ≠ X.toCombMap.faceOf d → IsRibbonAt X ι x →
          IsRibbonAt X' (fun a => T.embedding (ι a)) (T.embedding x)

/-- **One doubling in a face with at least two darts** (`FaceEdgeDoubling`). -/
theorem stepEdge (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (X : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (X.label d))
    (S : Finset X.toCombMap.Face) (d : X.toCombMap.Dart)
    (hS : X.toCombMap.faceOf d ∈ S) (hf : X.toCombMap.faceOf d ≠ X.outerFace)
    (hlen : 1 < (X.faceBoundary (X.toCombMap.faceOf d)).darts.length) :
    StepOutput D X S d := by
  generalize hfd : X.toCombMap.faceOf d = f at hS hf hlen
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (((X.faceBoundary f).mem_iff d).mpr hfd)
  rw [← FaceEdgeDoubling.dart_eq_get X f j] at hj
  subst hj
  have hemb : ∀ y,
      (FaceEdgeDoubling.collarTransport X f j hlen hf D hsymm hlabel hS).embedding y =
        embed X.toCombMap y := fun _ => rfl
  have hdig : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf
      (embed X.toCombMap (FaceEdgeDoubling.dart X f j)) = FaceEdgeDoubling.digon X f j hlen :=
    FaceEdgeDoubling.faceOf_embed_dart_digon X f j hlen
  have hface : ∀ x, x ≠ FaceEdgeDoubling.dart X f j →
      (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (embed X.toCombMap x) =
        FaceEdgeDoubling.faceImage X f j hlen (X.toCombMap.faceOf x) :=
    fun x hx => FaceEdgeDoubling.faceOf_diagram_embed_of_ne X f j hlen hf hx
  have houter : (FaceEdgeDoubling.diagram X f j hlen hf).outerFace =
      FaceEdgeDoubling.faceImage X f j hlen X.outerFace :=
    (FaceEdgeDoubling.faceImage_of_ne X f j hlen hf.symm).symm
  refine ⟨FaceEdgeDoubling.diagram X f j hlen hf, FaceEdgeDoubling.collarFaceSet X f j hlen S,
    FaceEdgeDoubling.collarTransport X f j hlen hf D hsymm hlabel hS,
    fun hred => FaceEdgeDoubling.reduced X f j hlen hf hred, ?_, ?_⟩
  · simp only [hemb]
    refine ⟨none, ?_, ?_, ?_, ?_, ?_⟩
    · exact FaceEdgeDoubling.isFaceCycle_collarDigon X f j hlen
    · intro y h
      cases h
    · rw [hdig]
      exact fun h => FaceEdgeDoubling.keep_ne_digon X f j hlen hf.symm h.symm
    · intro C hC
      rw [hdig]
      exact FaceEdgeDoubling.digon_not_collarCell X f j hlen hf C hC
    · rfl
  · intro x hx
    simp only [hemb]
    refine ⟨?_, ?_, ?_⟩
    · rw [hface x hx]
      exact FaceEdgeDoubling.mem_collarFaceSet_faceImage X f j hlen S _
    · rw [hface x hx, houter]
      exact not_congr (FaceEdgeDoubling.faceImage_injective X f j hlen).eq_iff
    · intro β ι hne hrib
      have hne' : X.toCombMap.faceOf x ≠ f := by
        rwa [FaceEdgeDoubling.dart_face X f j] at hne
      obtain ⟨c, hcyc, hnew, hout, hcell, hlab⟩ := hrib
      have hxc : x ≠ c := fun h => (List.nodup_cons.mp hcyc.nodup).1 (List.mem_singleton.mpr h)
      have hfc : X.toCombMap.faceOf c = X.toCombMap.faceOf x :=
        (hcyc.mem_iff c).mp (List.mem_cons_of_mem _ (List.mem_singleton_self c))
      have hfc' : X.toCombMap.faceOf c ≠ f := by
        rw [hfc]
        exact hne'
      have hpx : X.toCombMap.facePerm x = c := List.isChain_pair.mp hcyc.chain
      have hpc : X.toCombMap.facePerm c = x := hcyc.closes
      refine ⟨embed X.toCombMap c, ?_, ?_, ?_, ?_, ?_⟩
      · exact
          { ne_nil := List.cons_ne_nil _ _
            nodup := List.nodup_cons.mpr
              ⟨fun h => hxc (embed_injective X.toCombMap (List.mem_singleton.mp h)),
                List.nodup_singleton _⟩
            chain := List.isChain_pair.mpr
              (((FaceEdgeDoubling.embedding X f j hlen hf).facePerm x hne').trans
                (congrArg (FaceEdgeDoubling.embedding X f j hlen hf).darts hpx))
            closes :=
              ((FaceEdgeDoubling.embedding X f j hlen hf).facePerm c hfc').trans
                (congrArg (FaceEdgeDoubling.embedding X f j hlen hf).darts hpc) }
      · intro a h
        exact hnew a (embed_injective X.toCombMap h)
      · rw [hface x hx, houter]
        exact fun h => hout (FaceEdgeDoubling.faceImage_injective X f j hlen h)
      · intro C hC
        obtain ⟨C₀, hC₀, hCf⟩ :=
          FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f j hlen hf hC
        rw [hCf, hface x hx]
        exact fun h => hcell C₀ hC₀ (FaceEdgeDoubling.faceImage_injective X f j hlen h)
      · show X.label c = RelWord.inv (X.label x)
        exact hlab

/-- **One doubling in a monogon** (`MonogonDoubling`): the monogon `[d]` gets the new dart `none`,
and `d` moves onto the digon `[d, some none]`. -/
theorem stepMono (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (X : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (X.label d))
    (S : Finset X.toCombMap.Face) (d : X.toCombMap.Dart)
    (hS : X.toCombMap.faceOf d ∈ S) (hf : X.toCombMap.faceOf d ≠ X.outerFace)
    (hmono : (X.faceBoundary (X.toCombMap.faceOf d)).darts.length = 1) :
    StepOutput D X S d := by
  generalize hfd : X.toCombMap.faceOf d = f at hS hf hmono
  obtain rfl : MonogonDoubling.dart X f = d := MonogonDoubling.dart_eq_of_face X f hmono hfd
  have hemb : ∀ y,
      (MonogonDoubling.collarTransport X f hf hmono D hsymm hlabel hS).embedding y =
        embed X.toCombMap y := fun _ => rfl
  have hdig : (MonogonDoubling.diagram X f hf hmono).toCombMap.faceOf
      (embed X.toCombMap (MonogonDoubling.dart X f)) = MonogonDoubling.digon X f :=
    MonogonDoubling.faceOf_embed_of_face X f (MonogonDoubling.dart_face X f)
  have hne_f : ∀ x, x ≠ MonogonDoubling.dart X f → X.toCombMap.faceOf x ≠ f :=
    fun x hx h => hx (MonogonDoubling.dart_eq_of_face X f hmono h).symm
  have hface : ∀ x, x ≠ MonogonDoubling.dart X f →
      (MonogonDoubling.diagram X f hf hmono).toCombMap.faceOf (embed X.toCombMap x) =
        MonogonDoubling.faceImage X f (X.toCombMap.faceOf x) := fun x hx =>
    (MonogonDoubling.faceOf_embed_of_ne X f (hne_f x hx)).trans
      (MonogonDoubling.faceImage_of_ne X f (hne_f x hx)).symm
  have houter : (MonogonDoubling.diagram X f hf hmono).outerFace =
      MonogonDoubling.faceImage X f X.outerFace :=
    (MonogonDoubling.faceImage_of_ne X f hf.symm).symm
  refine ⟨MonogonDoubling.diagram X f hf hmono, MonogonDoubling.faceSet X f S,
    MonogonDoubling.collarTransport X f hf hmono D hsymm hlabel hS,
    fun hred => MonogonDoubling.reduced X f hf hmono hred, ?_, ?_⟩
  · simp only [hemb]
    refine ⟨some none, ?_, ?_, ?_, ?_, ?_⟩
    · exact MonogonDoubling.isFaceCycle_digon X f hmono
    · intro y h
      cases h
    · rw [hdig]
      exact fun h => MonogonDoubling.keep_ne_digon X f hf.symm h.symm
    · intro C hC
      rw [hdig]
      exact MonogonDoubling.digon_not_cell X f hf hmono C hC
    · rfl
  · intro x hx
    simp only [hemb]
    refine ⟨?_, ?_, ?_⟩
    · rw [hface x hx]
      exact MonogonDoubling.mem_faceSet_faceImage X f S _
    · rw [hface x hx, houter]
      exact not_congr (MonogonDoubling.faceImage_injective X f).eq_iff
    · intro β ι _ hrib
      have hne' := hne_f x hx
      obtain ⟨c, hcyc, hnew, hout, hcell, hlab⟩ := hrib
      have hxc : x ≠ c := fun h => (List.nodup_cons.mp hcyc.nodup).1 (List.mem_singleton.mpr h)
      have hfc : X.toCombMap.faceOf c = X.toCombMap.faceOf x :=
        (hcyc.mem_iff c).mp (List.mem_cons_of_mem _ (List.mem_singleton_self c))
      have hfc' : X.toCombMap.faceOf c ≠ f := by
        rw [hfc]
        exact hne'
      have hpx : X.toCombMap.facePerm x = c := List.isChain_pair.mp hcyc.chain
      have hpc : X.toCombMap.facePerm c = x := hcyc.closes
      refine ⟨embed X.toCombMap c, ?_, ?_, ?_, ?_, ?_⟩
      · exact
          { ne_nil := List.cons_ne_nil _ _
            nodup := List.nodup_cons.mpr
              ⟨fun h => hxc (embed_injective X.toCombMap (List.mem_singleton.mp h)),
                List.nodup_singleton _⟩
            chain := List.isChain_pair.mpr
              (((MonogonDoubling.embedding X f hf hmono).facePerm x hne').trans
                (congrArg (MonogonDoubling.embedding X f hf hmono).darts hpx))
            closes :=
              ((MonogonDoubling.embedding X f hf hmono).facePerm c hfc').trans
                (congrArg (MonogonDoubling.embedding X f hf hmono).darts hpc) }
      · intro a h
        exact hnew a (embed_injective X.toCombMap h)
      · rw [hface x hx, houter]
        exact fun h => hout (MonogonDoubling.faceImage_injective X f h)
      · intro C hC
        change C ∈ X.relatorCells.map (MonogonDoubling.cell X f hf) at hC
        obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
        rw [hface x hx]
        exact fun h => hcell C₀ hC₀ (MonogonDoubling.faceImage_injective X f h)
      · show X.label c = RelWord.inv (X.label x)
        exact hlab

/-- **One doubling**, in whichever form the face of `d` allows. -/
theorem step (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (X : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (X.label d))
    (S : Finset X.toCombMap.Face) (d : X.toCombMap.Dart)
    (hS : X.toCombMap.faceOf d ∈ S) (hf : X.toCombMap.faceOf d ≠ X.outerFace) :
    StepOutput D X S d := by
  have hpos : 0 < (X.faceBoundary (X.toCombMap.faceOf d)).darts.length :=
    List.length_pos_of_mem (((X.faceBoundary (X.toCombMap.faceOf d)).mem_iff d).mpr rfl)
  by_cases hmono : (X.faceBoundary (X.toCombMap.faceOf d)).darts.length = 1
  · exact stepMono D hsymm X hlabel S d hS hf hmono
  · exact stepEdge D hsymm X hlabel S d hS hf (by omega)

/-- **Doubling the rest of a list.**  The darts `r` already span ribbon cells and the darts `q`
still have to be doubled; together they are distinct.  Double `q` one dart at a time. -/
theorem aux (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {α : Type v}
    (q : List α) :
    ∀ (X : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (X.label d)) →
    ∀ (S : Finset X.toCombMap.Face) (ι : α → X.toCombMap.Dart) (r : List α),
      (r ++ q).Nodup → Function.Injective ι →
      (∀ a ∈ r, IsRibbonAt X ι (ι a)) →
      (∀ a ∈ q, X.toCombMap.faceOf (ι a) ∈ S ∧
        X.toCombMap.faceOf (ι a) ≠ X.outerFace) →
      ∃ (X' : DiscDiagram.{u, w, v} W) (S' : Finset X'.toCombMap.Face)
        (T : GeodesicCollar.Transport D S X' S'), (X.Reduced → X'.Reduced) ∧
        ∀ a ∈ r ++ q, IsRibbonAt X' (fun b => T.embedding (ι b)) (T.embedding (ι a)) := by
  induction q with
  | nil =>
      intro X hlabel S ι r _ _ hr _
      refine ⟨X, S, GeodesicCollar.Transport.refl D hlabel S, id, fun a ha => ?_⟩
      rw [List.append_nil] at ha
      exact (hr a ha).congr rfl (fun b => ⟨b, rfl⟩)
  | cons a₀ q ih =>
      intro X hlabel S ι r hnd hinj hr hq
      obtain ⟨hS, hf⟩ := hq a₀ List.mem_cons_self
      obtain ⟨X₁, S₁, T₁, hred₁, hnew, hold⟩ := step D hsymm X hlabel S (ι a₀) hS hf
      have hnd₁ : (r ++ [a₀] ++ q).Nodup := by
        rw [List.append_assoc, List.singleton_append]
        exact hnd
      have hinj₁ : Function.Injective (fun b => T₁.embedding (ι b)) :=
        T₁.embedding.injective.comp hinj
      have hr₁ : ∀ b ∈ r ++ [a₀],
          IsRibbonAt X₁ (fun b => T₁.embedding (ι b)) (T₁.embedding (ι b)) := by
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · have hba : b ≠ a₀ := (List.nodup_append.mp hnd).2.2 b hb a₀ List.mem_cons_self
          have hrib := hr b hb
          have hfne : X.toCombMap.faceOf (ι b) ≠ X.toCombMap.faceOf (ι a₀) := by
            obtain ⟨c, hcyc, hnewc, -⟩ := hrib
            intro h
            have hmem : ι a₀ ∈ [ι b, c] := (hcyc.mem_iff (ι a₀)).mpr h.symm
            rcases List.mem_cons.mp hmem with h₁ | h₁
            · exact hba (hinj h₁).symm
            · exact hnewc a₀ (List.mem_singleton.mp h₁)
          exact (hold (ι b) (fun h => hba (hinj h))).2.2 ι hfne hrib
        · obtain rfl := List.mem_singleton.mp hb
          exact hnew.congr rfl (fun b => ⟨ι b, rfl⟩)
      have hq₁ : ∀ b ∈ q, X₁.toCombMap.faceOf (T₁.embedding (ι b)) ∈ S₁ ∧
          X₁.toCombMap.faceOf (T₁.embedding (ι b)) ≠ X₁.outerFace := by
        intro b hb
        have hba : b ≠ a₀ := fun h =>
          (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (h ▸ hb)
        obtain ⟨h₁, h₂, -⟩ := hold (ι b) (fun h => hba (hinj h))
        obtain ⟨hS', hf'⟩ := hq b (List.mem_cons_of_mem _ hb)
        exact ⟨h₁.mpr hS', h₂.mpr hf'⟩
      obtain ⟨X₂, S₂, T₂, hred₂, hrib₂⟩ :=
        ih X₁ T₁.label_isLetter S₁ (fun b => T₁.embedding (ι b)) (r ++ [a₀]) hnd₁ hinj₁
          hr₁ hq₁
      refine ⟨X₂, S₂, T₁.trans T₂, fun h => hred₂ (hred₁ h), fun b hb => ?_⟩
      have hb' : b ∈ r ++ [a₀] ++ q := by
        rw [List.append_assoc, List.singleton_append]
        exact hb
      exact (hrib₂ b hb').congr rfl (fun c => ⟨c, rfl⟩)

/-- **A path doubled into a ribbon** (step 2 of the plan for GL06e residual (i)).  Let `p` be a
list of distinct darts of `Δ`, each on an inner face, and let the labels be letters of `D`, with
`D.base` closed under inverses.  Then there is a collar transport from the faces of `p` to an
O-equivalent diagram `Δ'` in which the image of every dart of `p` spans a ribbon cell, a G-digon
whose other side is a new dart reading the inverse letter.  The transport keeps the outer
boundary and every relator cell off the faces of `p`, its labels are letters of `D`, and `Δ'` is
reduced when `Δ` is. -/
theorem exists_pathRibbon (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (p : List Delta.toCombMap.Dart) (hnodup : p.Nodup)
    (hp : ∀ d ∈ p, Delta.toCombMap.faceOf d ≠ Delta.outerFace) :
    ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
      (T : GeodesicCollar.Transport D (p.map Delta.toCombMap.faceOf).toFinset Delta' S'),
      (Delta.Reduced → Delta'.Reduced) ∧
      ∀ d ∈ p, IsRibbonAt Delta' (fun x => T.embedding x) (T.embedding d) := by
  obtain ⟨Delta', S', T, hred, h⟩ :=
    aux D hsymm p Delta hlabel (p.map Delta.toCombMap.faceOf).toFinset id []
      (by simpa using hnodup) Function.injective_id (fun a ha => by simp at ha)
      (fun d hd => ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨d, hd, rfl⟩), hp d hd⟩)
  exact ⟨Delta', S', T, hred,
    fun d hd => (h d (by simpa using hd)).congr rfl (fun b => ⟨b, rfl⟩)⟩

end GroupApproximation.GGT.VanKampen.PathRibbon

#audit_axioms GroupApproximation.GGT.VanKampen.PathRibbon.IsRibbonAt.congr
#audit_axioms GroupApproximation.GGT.VanKampen.PathRibbon.IsRibbonAt.exists_faceOf_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PathRibbon.stepEdge
#audit_axioms GroupApproximation.GGT.VanKampen.PathRibbon.stepMono
#audit_axioms GroupApproximation.GGT.VanKampen.PathRibbon.step
#audit_axioms GroupApproximation.GGT.VanKampen.PathRibbon.aux
#audit_axioms GroupApproximation.GGT.VanKampen.PathRibbon.exists_pathRibbon
