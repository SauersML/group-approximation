import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingRun
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.GGT.VanKampen.SurgeryOuterSpurThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# One doubling of a bridge dart of an enclosed face set

`EnclosedBridgeDoublingSuccStatement` (`ClosedWalkEnclosedSubdiagramPieces`) removes the bridge
darts of an outside walk one edge at a time.  Let `d₀ = FaceEdgeDoubling.dart Δ f j` be a dart of
the walk whose reverse is on the walk too, with `f` its face.  `FaceEdgeDoubling.diagram` (for an
inner face) or `OuterSpurThickening.diagram` (for the exterior) inserts a digon along `d₀`.  The
image walk `outerWalk.map (image M d₀)` puts the new dart `some none` in the place of `d₀`, and the
enclosed faces gain the digon: `newFaces = insert digon (faces.map faceImage)`.

* `vertexOf_image`, `vertexOf_alpha_image`, `chain_image`, `closes_image`: the image walk is closed.
* `mem_iff_image`: its darts are the reverses of the boundary darts of `newFaces` and its bridge
  darts, exactly as before; `d₀` and its reverse are no longer bridge darts.
* `enclosedFaceSetSucc_diagram`, `enclosedFaceSetSucc_spurDiagram`: the doubled diagram carries an
  enclosed face set turning to its successor (`turn_next_image`).
* `dartWord_invDarts_diagram`, `dartWord_invDarts_spurDiagram`: the inverse walks read the same word.
* `length_filter_newFaces`: the enclosed faces hold as many relator cells.
* `bridgeCount_image_lt`: the number of bridge darts drops.

The darts of the image walk have the type `EdgeInsertion.Dart M`, which is the dart type of the
doubled map only up to unfolding; the proofs below pass through term-mode equalities rather than
rewriting across the two spellings.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Equiv SimpleClosedWalkSides EdgeInsertion Embedded HullSC

namespace EnclosedBridgeDoubling

open scoped Classical in
/-- The number of darts of a walk whose reverse is on the walk too. -/
noncomputable def bridgeCount {M : CombMap.{v}} (outerWalk : List M.Dart) : ℕ :=
  (outerWalk.filter fun d => M.alpha d ∈ outerWalk).length

section Step

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length) (hlen : 1 < (Delta.faceBoundary f).darts.length)

/-- The corner after the doubled dart. -/
abbrev corner : Delta.toCombMap.Dart :=
  secondCorner Delta.toCombMap (FaceEdgeDoubling.rebased Delta f j)
    (FaceEdgeDoubling.second Delta f j hlen)

theorem corner_ne : FaceEdgeDoubling.dart Delta f j ≠ corner Delta f j hlen :=
  corners_ne Delta.toCombMap (FaceEdgeDoubling.rebased Delta f j)
    (FaceEdgeDoubling.second Delta f j hlen) Nat.one_pos

theorem sigma_alpha_dart :
    Delta.toCombMap.sigma (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) =
      corner Delta f j hlen :=
  (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm Delta f j hlen).symm

theorem image_eq_dartImage (z : Delta.toCombMap.Dart) :
    image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) z =
      FaceEdgeDoubling.dartImage Delta f j hlen z := by
  by_cases hz : z = FaceEdgeDoubling.dart Delta f j
  · subst hz
    rw [image_self, FaceEdgeDoubling.Holding.dartImage_dart]
  · rw [image_of_ne hz, FaceEdgeDoubling.Holding.dartImage_of_ne Delta f j hlen hz]

theorem faceOf_image (z : Delta.toCombMap.Dart) :
    (FaceEdgeDoubling.map Delta f j hlen).faceOf
        (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) z) =
      FaceEdgeDoubling.faceImage Delta f j hlen (Delta.toCombMap.faceOf z) := by
  rw [image_eq_dartImage Delta f j hlen z]
  exact FaceEdgeDoubling.Holding.faceOf_dartImage Delta f j hlen z

open scoped Classical in
/-- The enclosed faces after the doubling: the images of the old ones, and the digon. -/
noncomputable def newFaces (faces : Finset Delta.toCombMap.Face) :
    Finset (FaceEdgeDoubling.map Delta f j hlen).Face :=
  insert (FaceEdgeDoubling.digon Delta f j hlen)
    (faces.map ⟨FaceEdgeDoubling.faceImage Delta f j hlen,
      FaceEdgeDoubling.faceImage_injective Delta f j hlen⟩)

theorem digon_mem_newFaces (faces : Finset Delta.toCombMap.Face) :
    FaceEdgeDoubling.digon Delta f j hlen ∈ newFaces Delta f j hlen faces := by
  classical
  exact Finset.mem_insert_self _ _

theorem faceImage_mem_newFaces_iff (faces : Finset Delta.toCombMap.Face)
    (g : Delta.toCombMap.Face) :
    FaceEdgeDoubling.faceImage Delta f j hlen g ∈ newFaces Delta f j hlen faces ↔ g ∈ faces := by
  classical
  simp only [newFaces, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro (h | ⟨y, hy, hyg⟩)
    · exact absurd h (FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen g)
    · rwa [← FaceEdgeDoubling.faceImage_injective Delta f j hlen hyg]
  · intro hg
    exact Or.inr ⟨g, hg, rfl⟩

/-! ## The image walk is closed -/

theorem vertexOf_image (z : Delta.toCombMap.Dart) :
    (FaceEdgeDoubling.map Delta f j hlen).vertexOf
        (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) z) =
      (FaceEdgeDoubling.map Delta f j hlen).vertexOf (embed Delta.toCombMap z) := by
  by_cases hz : z = FaceEdgeDoubling.dart Delta f j
  · subst hz
    rw [image_self, CombMap.vertexOf_eq_iff]
    exact ⟨1, by
      rw [zpow_one]
      exact GeodesicCollar.edgeInsertion_sigma_some_none (corner_ne Delta f j hlen)⟩
  · exact congrArg (FaceEdgeDoubling.map Delta f j hlen).vertexOf (image_of_ne hz)

theorem vertexOf_alpha_image (z : Delta.toCombMap.Dart) :
    (FaceEdgeDoubling.map Delta f j hlen).vertexOf ((FaceEdgeDoubling.map Delta f j hlen).alpha
        (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) z)) =
      (FaceEdgeDoubling.map Delta f j hlen).vertexOf
        (embed Delta.toCombMap (Delta.toCombMap.alpha z)) := by
  by_cases hz : z = FaceEdgeDoubling.dart Delta f j
  · subst hz
    rw [image_self]
    have h1 : (FaceEdgeDoubling.map Delta f j hlen).vertexOf none =
        (FaceEdgeDoubling.map Delta f j hlen).vertexOf
          (embed Delta.toCombMap (corner Delta f j hlen)) := by
      rw [CombMap.vertexOf_eq_iff]
      exact ⟨1, by rw [zpow_one]; exact sigma_none_apply _ _⟩
    change (FaceEdgeDoubling.map Delta f j hlen).vertexOf none = _
    rw [h1]
    refine (GeodesicCollar.edgeInsertion_vertexOf_embed_iff _ _ _ _ _).mpr ?_
    rw [← sigma_alpha_dart Delta f j hlen, CombMap.vertexOf_eq_iff]
    exact ⟨-1, by rw [zpow_neg_one]; exact Equiv.symm_apply_apply _ _⟩
  · exact congrArg (fun y => (FaceEdgeDoubling.map Delta f j hlen).vertexOf
      ((FaceEdgeDoubling.map Delta f j hlen).alpha y)) (image_of_ne hz)

theorem chain_image {outerWalk : List Delta.toCombMap.Dart}
    (hchain : outerWalk.IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e) :
    (outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))).IsChain fun d e =>
      (FaceEdgeDoubling.map Delta f j hlen).vertexOf ((FaceEdgeDoubling.map Delta f j hlen).alpha d) =
        (FaceEdgeDoubling.map Delta f j hlen).vertexOf e := by
  refine (List.isChain_map _).2 (hchain.imp fun x y hxy => ?_)
  show (FaceEdgeDoubling.map Delta f j hlen).vertexOf ((FaceEdgeDoubling.map Delta f j hlen).alpha
      (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) x)) =
    (FaceEdgeDoubling.map Delta f j hlen).vertexOf
      (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) y)
  rw [vertexOf_alpha_image, vertexOf_image]
  exact (GeodesicCollar.edgeInsertion_vertexOf_embed_iff _ _ _ _ _).mpr hxy

theorem closes_image {outerWalk : List Delta.toCombMap.Dart} (hne : outerWalk ≠ [])
    (hne' : outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) ≠ [])
    (hcloses : Delta.toCombMap.vertexOf (Delta.toCombMap.alpha (outerWalk.getLast hne)) =
      Delta.toCombMap.vertexOf (outerWalk.head hne)) :
    (FaceEdgeDoubling.map Delta f j hlen).vertexOf ((FaceEdgeDoubling.map Delta f j hlen).alpha
        ((outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))).getLast hne')) =
      (FaceEdgeDoubling.map Delta f j hlen).vertexOf
        ((outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))).head hne') := by
  rw [List.getLast_map, List.head_map, vertexOf_alpha_image, vertexOf_image]
  exact (GeodesicCollar.edgeInsertion_vertexOf_embed_iff _ _ _ _ _).mpr hcloses

/-! ## Membership -/

theorem mem_iff_image {faces : Finset Delta.toCombMap.Face} {outerWalk : List Delta.toCombMap.Dart}
    (hE : EnclosedFaceSet Delta faces outerWalk) (hd : FaceEdgeDoubling.dart Delta f j ∈ outerWalk)
    (y : (FaceEdgeDoubling.map Delta f j hlen).Dart) :
    y ∈ outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) ↔
      (FaceEdgeDoubling.map Delta f j hlen).faceOf y ∉ newFaces Delta f j hlen faces ∧
        ((FaceEdgeDoubling.map Delta f j hlen).faceOf ((FaceEdgeDoubling.map Delta f j hlen).alpha y) ∈
            newFaces Delta f j hlen faces ∨
          (FaceEdgeDoubling.map Delta f j hlen).alpha y ∈
            outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))) := by
  have hfd : Delta.toCombMap.faceOf (FaceEdgeDoubling.dart Delta f j) ∉ faces :=
    ((hE.mem_iff _).mp hd).1
  have hmem : ∀ z, embed Delta.toCombMap z ∈
      outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) ↔
        z ∈ outerWalk ∧ z ≠ FaceEdgeDoubling.dart Delta f j := by
    intro z
    simp only [List.mem_map, image_eq_embed_iff]
    constructor
    · rintro ⟨x, hx, rfl, hne⟩
      exact ⟨hx, hne⟩
    · rintro ⟨hz, hne⟩
      exact ⟨z, hz, rfl, hne⟩
  rcases y with _ | _ | z
  · have h1 : none ∉ outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) :=
      fun h => by
        obtain ⟨x, _, hx⟩ := List.mem_map.mp h
        exact image_ne_none _ _ hx
    rw [FaceEdgeDoubling.faceOf_none_digon]
    exact ⟨fun h => absurd h h1, fun h => absurd (digon_mem_newFaces ..) h.1⟩
  · have h1 : some none ∈ outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) :=
      List.mem_map.mpr ⟨_, hd, image_self _⟩
    have hface : (FaceEdgeDoubling.map Delta f j hlen).faceOf (some none) ∉
        newFaces Delta f j hlen faces := by
      have h := faceOf_image Delta f j hlen (FaceEdgeDoubling.dart Delta f j)
      rw [image_self] at h
      rw [h, faceImage_mem_newFaces_iff]
      exact hfd
    refine ⟨fun _ => ⟨hface, Or.inl ?_⟩, fun _ => h1⟩
    change (FaceEdgeDoubling.map Delta f j hlen).faceOf none ∈ _
    rw [FaceEdgeDoubling.faceOf_none_digon]
    exact digon_mem_newFaces ..
  · change embed Delta.toCombMap z ∈
        outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) ↔
      (FaceEdgeDoubling.map Delta f j hlen).faceOf (embed Delta.toCombMap z) ∉
          newFaces Delta f j hlen faces ∧
        ((FaceEdgeDoubling.map Delta f j hlen).faceOf
            (embed Delta.toCombMap (Delta.toCombMap.alpha z)) ∈ newFaces Delta f j hlen faces ∨
          embed Delta.toCombMap (Delta.toCombMap.alpha z) ∈
            outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)))
    by_cases hz : z = FaceEdgeDoubling.dart Delta f j
    · subst hz
      have h1 : embed Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) ∉
          outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) :=
        fun h => ((hmem _).mp h).2 rfl
      rw [FaceEdgeDoubling.faceOf_embed_dart_digon]
      exact ⟨fun h => absurd h h1, fun h => absurd (digon_mem_newFaces ..) h.1⟩
    · rw [hmem, ← image_of_ne hz, faceOf_image, faceImage_mem_newFaces_iff]
      have hold := hE.mem_iff z
      by_cases haz : Delta.toCombMap.alpha z = FaceEdgeDoubling.dart Delta f j
      · rw [haz, FaceEdgeDoubling.faceOf_embed_dart_digon]
        rw [haz] at hold
        simp only [hd, or_true, and_true] at hold
        exact ⟨fun h => ⟨hold.mp h.1, Or.inl (digon_mem_newFaces ..)⟩,
          fun h => ⟨hold.mpr h.1, hz⟩⟩
      · rw [← image_of_ne haz, faceOf_image, faceImage_mem_newFaces_iff, image_of_ne haz, hmem]
        constructor
        · rintro ⟨hzw, -⟩
          obtain ⟨h1, h2⟩ := hold.mp hzw
          exact ⟨h1, h2.imp id fun h => ⟨h, haz⟩⟩
        · rintro ⟨h1, h2⟩
          exact ⟨hold.mpr ⟨h1, h2.imp id And.left⟩, hz⟩

/-! ## Words and relator cells -/

theorem label_alpha_image (z : Delta.toCombMap.Dart) :
    FaceEdgeDoubling.label Delta f j hlen ((FaceEdgeDoubling.map Delta f j hlen).alpha
        (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) z)) =
      Delta.label (Delta.toCombMap.alpha z) := by
  by_cases hz : z = FaceEdgeDoubling.dart Delta f j
  · subst hz
    rw [image_self]
    exact (Delta.label_alpha _).symm
  · exact congrArg (fun y => FaceEdgeDoubling.label Delta f j hlen
      ((FaceEdgeDoubling.map Delta f j hlen).alpha y)) (image_of_ne hz)

theorem map_label_alpha_image (outerWalk : List Delta.toCombMap.Dart) :
    ((outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))).reverse.map
        (FaceEdgeDoubling.map Delta f j hlen).alpha).map (FaceEdgeDoubling.label Delta f j hlen) =
      (outerWalk.reverse.map Delta.toCombMap.alpha).map Delta.label := by
  have e1 : (outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))).reverse =
      outerWalk.reverse.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) :=
    List.map_reverse.symm
  have key : ∀ l : List Delta.toCombMap.Dart,
      List.map (FaceEdgeDoubling.label Delta f j hlen)
          (List.map (FaceEdgeDoubling.map Delta f j hlen).alpha
            (List.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) l)) =
        List.map Delta.label (List.map Delta.toCombMap.alpha l) := by
    intro l
    induction l with
    | nil => rfl
    | cons z zs ih =>
        show FaceEdgeDoubling.label Delta f j hlen ((FaceEdgeDoubling.map Delta f j hlen).alpha
            (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j) z)) ::
              List.map (FaceEdgeDoubling.label Delta f j hlen)
                (List.map (FaceEdgeDoubling.map Delta f j hlen).alpha
                  (List.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)) zs)) =
            Delta.label (Delta.toCombMap.alpha z) ::
              List.map Delta.label (List.map Delta.toCombMap.alpha zs)
        rw [label_alpha_image Delta f j hlen z, ih]
  exact (congrArg (fun l => List.map (FaceEdgeDoubling.label Delta f j hlen)
    (List.map (FaceEdgeDoubling.map Delta f j hlen).alpha l)) e1).trans (key outerWalk.reverse)

open scoped Classical in
theorem length_filter_newFaces {outer' : (FaceEdgeDoubling.map Delta f j hlen).Face}
    (cells : List (RelatorCell Delta.toCombMap Delta.outerFace W))
    (cellImage : RelatorCell Delta.toCombMap Delta.outerFace W →
      RelatorCell (FaceEdgeDoubling.map Delta f j hlen) outer' W)
    (hface : ∀ C, (cellImage C).face = FaceEdgeDoubling.faceImage Delta f j hlen C.face)
    (faces : Finset Delta.toCombMap.Face) :
    ((cells.map cellImage).filter fun C => C.face ∈ newFaces Delta f j hlen faces).length =
      (cells.filter fun C => C.face ∈ faces).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun C _ => ?_
  simp only [Function.comp_apply, hface, faceImage_mem_newFaces_iff]

/-- A filter by a stronger predicate that misses a point of the weaker one is shorter.  Stated for
arbitrary `Bool` predicates, so that it applies whatever decidability instances the filters carry. -/
theorem length_filter_lt_of_imp {α : Type*} {p q : α → Bool} {l : List α}
    (himp : ∀ x ∈ l, p x = true → q x = true) {x : α} (hx : x ∈ l) (hqx : q x = true)
    (hpx : ¬ p x = true) : (l.filter p).length < (l.filter q).length := by
  have hsub : l.filter p = (l.filter q).filter p := by
    rw [List.filter_filter]
    refine List.filter_congr fun z hz => ?_
    by_cases hp : p z = true
    · simp [hp, himp z hz hp]
    · simp [hp]
  rw [hsub]
  exact List.length_filter_lt_length_iff_exists.mpr ⟨x, List.mem_filter.mpr ⟨hx, hqx⟩, hpx⟩

open scoped Classical in
/-- **The number of bridge darts drops**: `d₀` and its reverse stop being bridge darts, and no
bridge dart is created. -/
theorem bridgeCount_image_lt {outerWalk : List Delta.toCombMap.Dart}
    (hd : FaceEdgeDoubling.dart Delta f j ∈ outerWalk)
    (had : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j) ∈ outerWalk) :
    bridgeCount (M := FaceEdgeDoubling.map Delta f j hlen)
        (outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))) <
      bridgeCount (M := Delta.toCombMap) outerWalk := by
  unfold bridgeCount
  rw [List.filter_map, List.length_map]
  refine length_filter_lt_of_imp (fun z _ hz => ?_) hd ?_ ?_
  · simp only [Function.comp_apply, decide_eq_true_eq] at hz ⊢
    by_cases hzd : z = FaceEdgeDoubling.dart Delta f j
    · subst hzd
      rw [image_self] at hz
      obtain ⟨x, _, hx⟩ := List.mem_map.mp hz
      exact absurd hx (image_ne_none _ _)
    · rw [image_of_ne hzd] at hz
      obtain ⟨x, hx, hxz⟩ := List.mem_map.mp hz
      rw [← (image_eq_embed_iff.mp hxz).1]
      exact hx
  · simp only [decide_eq_true_eq]
    exact had
  · simp only [Function.comp_apply, image_self, decide_eq_true_eq]
    intro h
    obtain ⟨x, _, hx⟩ := List.mem_map.mp h
    exact absurd hx (image_ne_none _ _)

/-! ## The doubled diagrams -/

open scoped Classical in
/-- **The doubling of a bridge dart on an inner face.** -/
theorem enclosedFaceSetSucc_diagram (hf : f ≠ Delta.outerFace) {faces : Finset Delta.toCombMap.Face}
    {outerWalk : List Delta.toCombMap.Dart} (E : EnclosedFaceSetSucc Delta faces outerWalk)
    (hd : FaceEdgeDoubling.dart Delta f j ∈ outerWalk)
    (had : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j) ∈ outerWalk) :
    EnclosedFaceSetSucc (FaceEdgeDoubling.diagram Delta f j hlen hf) (newFaces Delta f j hlen faces)
      (outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j))) where
  outerFace_not_mem := by
    change FaceEdgeDoubling.keep Delta f j hlen Delta.outerFace ∉ _
    intro h
    have h' : FaceEdgeDoubling.faceImage Delta f j hlen Delta.outerFace ∈
        newFaces Delta f j hlen faces :=
      (congrArg (· ∈ newFaces Delta f j hlen faces)
        (FaceEdgeDoubling.faceImage_of_ne Delta f j hlen (Ne.symm hf))).mpr h
    exact E.outerFace_not_mem ((faceImage_mem_newFaces_iff Delta f j hlen faces _).mp h')
  ne_nil := by simpa using E.ne_nil
  nodup := E.nodup.map (image_injective _)
  chain := chain_image Delta f j hlen E.chain
  closes := closes_image Delta f j hlen E.ne_nil _ E.closes
  mem_iff := mem_iff_image Delta f j hlen E.toEnclosedFaceSet hd
  turn_mem := by
    intro y hy m hm hkeep hfirst
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have h := turn_next_image (corner_ne Delta f j hlen) (sigma_alpha_dart Delta f j hlen) hd had
      E.turn_next i hi m hm hkeep hfirst
    exact (congrArg (· ∈ outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)))
      h).mpr (List.getElem_mem _)
  turn_next := turn_next_image (corner_ne Delta f j hlen) (sigma_alpha_dart Delta f j hlen) hd had
    E.turn_next

theorem dartWord_invDarts_diagram (hf : f ≠ Delta.outerFace) (outerWalk : List Delta.toCombMap.Dart) :
    dartWord (FaceEdgeDoubling.diagram Delta f j hlen hf)
        (invDarts (FaceEdgeDoubling.diagram Delta f j hlen hf)
          (outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)))) =
      dartWord Delta (invDarts Delta outerWalk) :=
  map_label_alpha_image Delta f j hlen outerWalk

open scoped Classical in
theorem length_filter_diagram (hf : f ≠ Delta.outerFace) (faces : Finset Delta.toCombMap.Face) :
    ((FaceEdgeDoubling.diagram Delta f j hlen hf).relatorCells.filter fun C =>
        C.face ∈ newFaces Delta f j hlen faces).length =
      (Delta.relatorCells.filter fun C => C.face ∈ faces).length :=
  length_filter_newFaces Delta f j hlen Delta.relatorCells (FaceEdgeDoubling.cell Delta f j hlen hf)
    (fun _ => rfl) faces

end Step

section Spur

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

open scoped Classical in
/-- **The doubling of a bridge dart on the exterior.** -/
theorem enclosedFaceSetSucc_spurDiagram {faces : Finset Delta.toCombMap.Face}
    {outerWalk : List Delta.toCombMap.Dart} (E : EnclosedFaceSetSucc Delta faces outerWalk)
    (hd : FaceEdgeDoubling.dart Delta Delta.outerFace j ∈ outerWalk)
    (had : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∈ outerWalk) :
    EnclosedFaceSetSucc (OuterSpurThickening.diagram Delta j hlen)
      (newFaces Delta Delta.outerFace j hlen faces)
      (outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta Delta.outerFace j))) where
  outerFace_not_mem := by
    change FaceEdgeDoubling.cellFace Delta Delta.outerFace j hlen ∉ _
    intro h
    have h' : FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen Delta.outerFace ∈
        newFaces Delta Delta.outerFace j hlen faces :=
      (congrArg (· ∈ newFaces Delta Delta.outerFace j hlen faces)
        (FaceEdgeDoubling.faceImage_self Delta Delta.outerFace j hlen)).mpr h
    exact E.outerFace_not_mem
      ((faceImage_mem_newFaces_iff Delta Delta.outerFace j hlen faces _).mp h')
  ne_nil := by simpa using E.ne_nil
  nodup := E.nodup.map (image_injective _)
  chain := chain_image Delta Delta.outerFace j hlen E.chain
  closes := closes_image Delta Delta.outerFace j hlen E.ne_nil _ E.closes
  mem_iff := mem_iff_image Delta Delta.outerFace j hlen E.toEnclosedFaceSet hd
  turn_mem := by
    intro y hy m hm hkeep hfirst
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have h := turn_next_image (corner_ne Delta Delta.outerFace j hlen)
      (sigma_alpha_dart Delta Delta.outerFace j hlen) hd had E.turn_next i hi m hm hkeep hfirst
    exact (congrArg
      (· ∈ outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta Delta.outerFace j)))
      h).mpr (List.getElem_mem _)
  turn_next := turn_next_image (corner_ne Delta Delta.outerFace j hlen)
    (sigma_alpha_dart Delta Delta.outerFace j hlen) hd had E.turn_next

theorem dartWord_invDarts_spurDiagram (outerWalk : List Delta.toCombMap.Dart) :
    dartWord (OuterSpurThickening.diagram Delta j hlen)
        (invDarts (OuterSpurThickening.diagram Delta j hlen)
          (outerWalk.map (image Delta.toCombMap (FaceEdgeDoubling.dart Delta Delta.outerFace j)))) =
      dartWord Delta (invDarts Delta outerWalk) :=
  map_label_alpha_image Delta Delta.outerFace j hlen outerWalk

open scoped Classical in
theorem length_filter_spurDiagram (faces : Finset Delta.toCombMap.Face) :
    ((OuterSpurThickening.diagram Delta j hlen).relatorCells.filter fun C =>
        C.face ∈ newFaces Delta Delta.outerFace j hlen faces).length =
      (Delta.relatorCells.filter fun C => C.face ∈ faces).length :=
  length_filter_newFaces Delta Delta.outerFace j hlen Delta.relatorCells
    (OuterSpurThickening.spurCell Delta j hlen) (fun _ => rfl) faces

end Spur

end EnclosedBridgeDoubling

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.EnclosedBridgeDoubling

#audit_axioms mem_iff_image
#audit_axioms length_filter_lt_of_imp
#audit_axioms bridgeCount_image_lt
#audit_axioms enclosedFaceSetSucc_diagram
#audit_axioms dartWord_invDarts_diagram
#audit_axioms length_filter_diagram
#audit_axioms enclosedFaceSetSucc_spurDiagram
#audit_axioms dartWord_invDarts_spurDiagram
#audit_axioms length_filter_spurDiagram
