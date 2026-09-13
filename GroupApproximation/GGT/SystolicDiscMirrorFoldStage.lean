import GroupApproximation.GGT.SystolicDiscMovesAdapter
import GroupApproximation.GGT.VanKampen.EdgeDeletionFaceCycles
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Fold stages (HC6, the mirror fold)

A mirror pair of inner triangles `d, alpha d` with equal third vertices folds away in a few
map surgeries.  The intermediate maps are not triangulated discs: some faces are digons
waiting to be deleted.  A `FoldStage X` is the working form: a labelled map with an explicit
exterior face cycle and a face-invariant set `bad` of pending darts, every face off the
exterior cycle and off the pending darts being a triangle of `X`.

* `FoldStage.tri_of_embed`: triangles transport along an injective map of darts commuting
  with face rotation.
* `FoldStage.toStage`, `FoldStage.toStage_boundary`: a triangulated disc is a stage with
  nothing pending.
* `FoldStage.exists_triangulatedDisc`: a planar stage with nothing pending is a triangulated
  disc with the same boundary and the same faces.
* `FoldStage.deleteDigon`: deleting the edge of a pending digon `a, b` keeps the boundary
  (`deleteDigon_boundary`), keeps planarity (`deleteDigon_planar`) and removes one face
  (`deleteDigon_faceCount`).
-/

namespace GroupApproximation.Systolic

open GGT.VanKampen

universe u

variable {V : Type u} (X : TriangleComplex V)

/-- **A disc under folding.**  A labelled map with an explicit exterior face cycle and a
face-invariant set of pending darts; every face off the exterior cycle and off the pending
darts is a triangle of `X`. -/
structure FoldStage where
  /-- The map. -/
  map : CombMap.{0}
  /-- The labels, constant along vertex rotation. -/
  lab : map.Dart → V
  lab_sigma : ∀ d, lab (map.sigma d) = lab d
  /-- Every edge lies on an edge of `X`. -/
  adj : ∀ d, X.G.Adj (lab d) (lab (map.alpha d))
  /-- The exterior face. -/
  cyc : List map.Dart
  isFaceCycle : map.IsFaceCycle cyc
  /-- The pending darts. -/
  bad : map.Dart → Prop
  bad_facePerm : ∀ d, bad (map.facePerm d) ↔ bad d
  cyc_bad : ∀ z ∈ cyc, ¬ bad z
  /-- Every other face is a triangle of `X`. -/
  tri : ∀ d, d ∉ cyc → ¬ bad d → (map.facePerm ^ 3) d = d ∧
    X.Tri (lab d) (lab (map.facePerm d)) (lab ((map.facePerm ^ 2) d))

variable {X}

/-- Face rotation keeps a dart on or off a face cycle. -/
theorem isFaceCycle_facePerm_mem_iff {M : CombMap.{0}} {l : List M.Dart}
    (hl : M.IsFaceCycle l) (x : M.Dart) : M.facePerm x ∈ l ↔ x ∈ l := by
  rw [hl.mem_iff, hl.mem_iff, M.faceOf_facePerm]

namespace FoldStage

/-- The boundary vertex walk, closed up at the first vertex. -/
def boundary (S : FoldStage X) : List V :=
  S.cyc.map S.lab ++ [S.lab (S.cyc.head S.isFaceCycle.ne_nil)]

/-- Two stages whose exterior cycles read the same labels have the same boundary. -/
theorem boundary_eq_of_map_lab {S T : FoldStage X} (h : T.cyc.map T.lab = S.cyc.map S.lab) :
    T.boundary = S.boundary := by
  have h1 := congrArg List.head? h
  rw [List.head?_map, List.head?_map, List.head?_eq_some_head T.isFaceCycle.ne_nil,
    List.head?_eq_some_head S.isFaceCycle.ne_nil] at h1
  have hxy : T.lab (T.cyc.head T.isFaceCycle.ne_nil) =
      S.lab (S.cyc.head S.isFaceCycle.ne_nil) :=
    Option.some.inj h1
  unfold boundary
  rw [h, hxy]

/-- Labels across one face rotation. -/
theorem lab_facePerm (S : FoldStage X) (z : S.map.Dart) :
    S.lab (S.map.facePerm z) = S.lab (S.map.alpha z) :=
  S.lab_sigma (S.map.alpha z)

/-- **Triangles transport along an embedding.**  Let `τ` be an injective map of the darts of
`N` into a stage, keeping labels, sending darts off the exterior cycle and off the pending
darts of `N` to such darts, and commuting there with face rotation.  Then every face of `N`
off its exterior cycle and off its pending darts is a triangle of `X`. -/
theorem tri_of_embed (S : FoldStage X) {N : CombMap.{0}} (lab : N.Dart → V)
    {cyc : List N.Dart} (hcyc : N.IsFaceCycle cyc) (bad : N.Dart → Prop)
    (hbad : ∀ d, bad (N.facePerm d) ↔ bad d) (τ : N.Dart → S.map.Dart)
    (hτ : Function.Injective τ) (hlab : ∀ x, lab x = S.lab (τ x))
    (hmem : ∀ x, x ∉ cyc → τ x ∉ S.cyc) (hgood : ∀ x, ¬ bad x → ¬ S.bad (τ x))
    (hcomm : ∀ x, x ∉ cyc → ¬ bad x → τ (N.facePerm x) = S.map.facePerm (τ x))
    (x : N.Dart) (hx : x ∉ cyc) (hxb : ¬ bad x) :
    (N.facePerm ^ 3) x = x ∧
      X.Tri (lab x) (lab (N.facePerm x)) (lab ((N.facePerm ^ 2) x)) := by
  have hx1 : N.facePerm x ∉ cyc := fun hm => hx ((isFaceCycle_facePerm_mem_iff hcyc x).mp hm)
  have hxb1 : ¬ bad (N.facePerm x) := fun hm => hxb ((hbad x).mp hm)
  have hx2 : N.facePerm (N.facePerm x) ∉ cyc := fun hm =>
    hx1 ((isFaceCycle_facePerm_mem_iff hcyc _).mp hm)
  have hxb2 : ¬ bad (N.facePerm (N.facePerm x)) := fun hm => hxb1 ((hbad _).mp hm)
  obtain ⟨h3, ht⟩ := S.tri (τ x) (hmem x hx) (hgood x hxb)
  have e1 : τ (N.facePerm x) = S.map.facePerm (τ x) := hcomm x hx hxb
  have e2 : τ ((N.facePerm ^ 2) x) = (S.map.facePerm ^ 2) (τ x) := by
    rw [perm_pow_two_apply, perm_pow_two_apply, hcomm _ hx1 hxb1, e1]
  have e3 : τ ((N.facePerm ^ 3) x) = (S.map.facePerm ^ 3) (τ x) := by
    rw [perm_pow_three_apply, perm_pow_three_apply, hcomm _ hx2 hxb2, hcomm _ hx1 hxb1, e1]
  refine ⟨hτ (e3.trans h3), ?_⟩
  rw [hlab x, hlab (N.facePerm x), hlab ((N.facePerm ^ 2) x), e1, e2]
  exact ht

/-! ### Triangulated discs as stages -/

/-- The exterior face of a triangulated disc, enumerated from its base dart. -/
theorem exists_outer_rest {γ : List V} (T : TriangulatedDisc X γ) :
    ∃ rest : List T.map.Dart, T.map.IsFaceCycle (T.base :: rest) := by
  obtain ⟨l, hl, hhead⟩ := T.map.exists_isFaceCycle_head T.base
  refine ⟨l.tail, ?_⟩
  rw [← hhead, List.cons_head_tail]
  exact hl

/-- **A triangulated disc as a stage with nothing pending.** -/
noncomputable def toStage {γ : List V} (T : TriangulatedDisc X γ) : FoldStage X where
  map := T.map
  lab := fun d => T.vtx (T.map.vertexOf d)
  lab_sigma := fun d => congrArg T.vtx (T.map.vertexOf_sigma d)
  adj := T.adj
  cyc := T.base :: (exists_outer_rest T).choose
  isFaceCycle := (exists_outer_rest T).choose_spec
  bad := fun _ => False
  bad_facePerm := fun _ => Iff.rfl
  cyc_bad := fun _ _ h => h
  tri := fun d hd _ => T.tri d (fun hface =>
    hd (((exists_outer_rest T).choose_spec.mem_iff d).mpr (hface.trans T.base_outer.symm)))

/-- The stage of a triangulated disc has the boundary of the disc. -/
theorem toStage_boundary {γ : List V} (T : TriangulatedDisc X γ) :
    (toStage T).boundary = γ := by
  refine Eq.trans ?_ T.boundary
  have hcyc := (exists_outer_rest T).choose_spec
  have hdeg : T.map.faceDegree T.outer = (T.base :: (exists_outer_rest T).choose).length := by
    rw [← T.base_outer]
    exact hcyc.length_eq.symm
  show (T.base :: (exists_outer_rest T).choose).map (fun d => T.vtx (T.map.vertexOf d)) ++
      [T.vtx (T.map.vertexOf ((T.base :: (exists_outer_rest T).choose).head hcyc.ne_nil))] = _
  rw [hdeg]
  exact (ofFn_boundary_eq hcyc (fun d => T.vtx (T.map.vertexOf d))).symm

/-- A planar stage with nothing pending is a cycle disc. -/
def toCycleDisc (S : FoldStage X) (hS : S.map.IsPlanar) (hgood : ∀ d, ¬ S.bad d) :
    CycleDisc X where
  map := S.map
  planar := hS
  lab := S.lab
  lab_sigma := S.lab_sigma
  adj := S.adj
  cyc := S.cyc
  isFaceCycle := S.isFaceCycle
  tri := fun d hd => S.tri d hd (hgood d)

/-- **A planar stage with nothing pending is a triangulated disc** with the same boundary
and the same faces. -/
theorem exists_triangulatedDisc {γ : List V} (S : FoldStage X) (hS : S.map.IsPlanar)
    (hgood : ∀ d, ¬ S.bad d) (hb : S.boundary = γ) :
    ∃ D : TriangulatedDisc X γ, D.innerFaceCount + 1 = S.map.faceCount := by
  subst hb
  have h1 : 1 ≤ S.map.faceCount := (S.toCycleDisc hS hgood).toTriangulatedDisc.one_le_faceCount
  refine ⟨(S.toCycleDisc hS hgood).toTriangulatedDisc, ?_⟩
  show S.map.faceCount - 1 + 1 = S.map.faceCount
  omega

/-! ### Deleting an edge -/

section Deletion

open scoped Classical

variable (S : FoldStage X) (a : S.map.Dart)

/-- Labels read through `EdgeDeletion.value` stay constant along vertex rotation. -/
theorem deletion_lab_sigma (x : (EdgeDeletion.toCombMap S.map a).Dart) :
    S.lab (EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).sigma x)) =
      S.lab (EdgeDeletion.value S.map a x) := by
  have hv := (EdgeDeletion.vertexOf_eq_iff S.map a _ x).mp
    ((EdgeDeletion.toCombMap S.map a).vertexOf_sigma x)
  rw [CombMap.vertexOf_eq_iff] at hv
  exact OrbitClassifier.eq_of_sameCycle S.map.sigma S.lab S.lab_sigma hv

/-- After deleting an edge, every edge still lies on an edge of `X`. -/
theorem deletion_adj (x : (EdgeDeletion.toCombMap S.map a).Dart) :
    X.G.Adj (S.lab (EdgeDeletion.value S.map a x))
      (S.lab (EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).alpha x))) := by
  rw [show EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).alpha x) =
    S.map.alpha (EdgeDeletion.value S.map a x) from EdgeDeletion.alpha_val S.map a x]
  exact S.adj _

/-- The darts of the deleted map placed back in the stage: the surviving dart `b` of a
digon `a, b` takes the place of `alpha a`. -/
noncomputable def digonEmbed (b : S.map.Dart) (x : EdgeDeletion.Dart S.map a) : S.map.Dart :=
  if EdgeDeletion.value S.map a x = b then S.map.alpha a else EdgeDeletion.value S.map a x

/-- Back from the stage: `alpha a` is read as `b`. -/
noncomputable def digonRho (b : S.map.Dart) (z : S.map.Dart) : S.map.Dart :=
  if z = S.map.alpha a then b else z

end Deletion

/-- **A pending digon.**  `a, b` is a face of length two, `a` is pending, the edge of `a` is
not the edge of `b`, and the pending darts other than `a, b` lie in the face-invariant set
`rest` of pending darts. -/
structure IsDigon (S : FoldStage X) (a b : S.map.Dart) (rest : S.map.Dart → Prop) : Prop where
  fwd : S.map.facePerm a = b
  bwd : S.map.facePerm b = a
  alpha_ne : S.map.alpha a ≠ b
  bad_a : S.bad a
  rest_facePerm : ∀ z, rest (S.map.facePerm z) ↔ rest z
  bad_imp : ∀ z, S.bad z → z = a ∨ z = b ∨ rest z
  rest_imp : ∀ z, rest z → S.bad z

namespace IsDigon

variable {S : FoldStage X} {a b : S.map.Dart} {rest : S.map.Dart → Prop}

theorem ne (h : IsDigon S a b rest) : a ≠ b := fun hab =>
  (S.adj a).ne (by rw [← S.lab_facePerm a, h.fwd, hab])

theorem bad_b (h : IsDigon S a b rest) : S.bad b := by
  rw [← h.fwd]
  exact (S.bad_facePerm a).mpr h.bad_a

theorem not_mem_a (h : IsDigon S a b rest) : a ∉ S.cyc := fun hm => S.cyc_bad a hm h.bad_a

theorem not_mem_b (h : IsDigon S a b rest) : b ∉ S.cyc := fun hm => S.cyc_bad b hm h.bad_b

theorem ne_b_of_mem (h : IsDigon S a b rest) {z : S.map.Dart} (hz : z ∈ S.cyc) : z ≠ b :=
  fun hzb => h.not_mem_b (by rwa [hzb] at hz)

theorem isFaceCycle (h : IsDigon S a b rest) : S.map.IsFaceCycle [a, b] :=
  ⟨List.cons_ne_nil _ _,
    List.nodup_cons.mpr ⟨fun hm => h.ne (List.mem_singleton.mp hm), List.nodup_singleton b⟩,
    List.isChain_cons_cons.mpr ⟨h.fwd, List.isChain_singleton _⟩, h.bwd⟩

/-- The two sides of the edge of `a` lie on different faces. -/
theorem face_ne (h : IsDigon S a b rest) : S.map.faceOf a ≠ S.map.faceOf (S.map.alpha a) := by
  intro hf
  have hm : S.map.alpha a ∈ [a, b] := (h.isFaceCycle.mem_iff (S.map.alpha a)).mpr hf.symm
  rcases List.mem_cons.mp hm with h1 | h1
  · exact S.map.alpha_fixedPointFree a h1
  · exact h.alpha_ne (List.mem_singleton.mp h1)

theorem lab_b (h : IsDigon S a b rest) : S.lab b = S.lab (S.map.alpha a) := by
  rw [← h.fwd]
  exact S.lab_facePerm a

end IsDigon

section Digon

open scoped Classical

variable {S : FoldStage X} {a b : S.map.Dart} {rest : S.map.Dart → Prop}

theorem digonEmbed_of_eq {x : EdgeDeletion.Dart S.map a}
    (hx : EdgeDeletion.value S.map a x = b) : digonEmbed S a b x = S.map.alpha a :=
  if_pos hx

theorem digonEmbed_of_ne {x : EdgeDeletion.Dart S.map a}
    (hx : EdgeDeletion.value S.map a x ≠ b) :
    digonEmbed S a b x = EdgeDeletion.value S.map a x :=
  if_neg hx

theorem digonRho_of_eq : digonRho S a b (S.map.alpha a) = b :=
  if_pos rfl

theorem digonRho_of_ne {z : S.map.Dart} (hz : z ≠ S.map.alpha a) : digonRho S a b z = z :=
  if_neg hz

theorem digonEmbed_ne_a (x : EdgeDeletion.Dart S.map a) : digonEmbed S a b x ≠ a := by
  by_cases hx : EdgeDeletion.value S.map a x = b
  · rw [digonEmbed_of_eq hx]
    exact S.map.alpha_fixedPointFree a
  · rw [digonEmbed_of_ne hx]
    exact EdgeDeletion.value_ne S.map a x

theorem digonEmbed_ne_b (h : IsDigon S a b rest) (x : EdgeDeletion.Dart S.map a) :
    digonEmbed S a b x ≠ b := by
  by_cases hx : EdgeDeletion.value S.map a x = b
  · rw [digonEmbed_of_eq hx]
    exact h.alpha_ne
  · rw [digonEmbed_of_ne hx]
    exact hx

theorem digonRho_embed (x : EdgeDeletion.Dart S.map a) :
    digonRho S a b (digonEmbed S a b x) = EdgeDeletion.value S.map a x := by
  by_cases hx : EdgeDeletion.value S.map a x = b
  · rw [digonEmbed_of_eq hx, digonRho_of_eq, hx]
  · rw [digonEmbed_of_ne hx, digonRho_of_ne (EdgeDeletion.value_ne_reverse S.map a x)]

theorem digonEmbed_injective : Function.Injective (digonEmbed S a b) := by
  intro x y hxy
  apply EdgeDeletion.value_injective S.map a
  rw [← digonRho_embed (b := b) x, ← digonRho_embed (b := b) y, hxy]

theorem lab_digonEmbed (h : IsDigon S a b rest) (x : EdgeDeletion.Dart S.map a) :
    S.lab (EdgeDeletion.value S.map a x) = S.lab (digonEmbed S a b x) := by
  by_cases hx : EdgeDeletion.value S.map a x = b
  · rw [digonEmbed_of_eq hx, hx, h.lab_b]
  · rw [digonEmbed_of_ne hx]

theorem lab_digonRho (h : IsDigon S a b rest) (z : S.map.Dart) :
    S.lab (digonRho S a b z) = S.lab z := by
  by_cases hz : z = S.map.alpha a
  · rw [hz, digonRho_of_eq, h.lab_b]
  · rw [digonRho_of_ne hz]

theorem digonRho_ne_a (h : IsDigon S a b rest) {z : S.map.Dart} (hz : z ≠ a) :
    digonRho S a b z ≠ a := by
  by_cases hza : z = S.map.alpha a
  · rw [hza, digonRho_of_eq]
    exact h.ne.symm
  · rw [digonRho_of_ne hza]
    exact hz

theorem digonRho_ne_alpha (h : IsDigon S a b rest) (z : S.map.Dart) :
    digonRho S a b z ≠ S.map.alpha a := by
  by_cases hza : z = S.map.alpha a
  · rw [hza, digonRho_of_eq]
    exact fun hb => h.alpha_ne hb.symm
  · rw [digonRho_of_ne hza]
    exact hza

theorem digonRho_inj {z w : S.map.Dart} (hz : z ≠ b) (hw : w ≠ b)
    (hzw : digonRho S a b z = digonRho S a b w) : z = w := by
  by_cases hza : z = S.map.alpha a
  · by_cases hwa : w = S.map.alpha a
    · rw [hza, hwa]
    · rw [hza, digonRho_of_eq, digonRho_of_ne hwa] at hzw
      exact absurd hzw.symm hw
  · by_cases hwa : w = S.map.alpha a
    · rw [hwa, digonRho_of_eq, digonRho_of_ne hza] at hzw
      exact absurd hzw hz
    · rwa [digonRho_of_ne hza, digonRho_of_ne hwa] at hzw

/-- **Face rotation after deleting the edge of a digon**, read back in the stage. -/
theorem digonEmbed_facePerm (h : IsDigon S a b rest) (x : EdgeDeletion.Dart S.map a) :
    digonEmbed S a b ((EdgeDeletion.toCombMap S.map a).facePerm x) =
      S.map.facePerm (digonEmbed S a b x) := by
  have hv := EdgeDeletion.value_facePerm_eq_next S.map a x
  have hfa : S.map.facePerm a ≠ a := fun ha => h.ne (ha.symm.trans h.fwd)
  by_cases hx : EdgeDeletion.value S.map a x = b
  · rw [digonEmbed_of_eq hx]
    by_cases hf : S.map.facePerm (S.map.alpha a) = S.map.alpha a
    · have hn : EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).facePerm x) = b := by
        rw [hv, hx, EdgeDeletion.next, if_pos h.bwd, if_pos hf, h.fwd]
      rw [digonEmbed_of_eq hn, hf]
    · have hn : EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).facePerm x) =
          S.map.facePerm (S.map.alpha a) := by
        rw [hv, hx, EdgeDeletion.next, if_pos h.bwd, if_neg hf]
      have hn' : EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).facePerm x) ≠ b := by
        rw [hn]
        exact fun hb => S.map.alpha_fixedPointFree a
          (S.map.facePerm.injective (hb.trans h.fwd.symm))
      rw [digonEmbed_of_ne hn', hn]
  · rw [digonEmbed_of_ne hx]
    have h1 : S.map.facePerm (EdgeDeletion.value S.map a x) ≠ a := fun hb =>
      hx (S.map.facePerm.injective (hb.trans h.bwd.symm))
    by_cases h2 : S.map.facePerm (EdgeDeletion.value S.map a x) = S.map.alpha a
    · have hn : EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).facePerm x) = b := by
        rw [hv, EdgeDeletion.next, if_neg h1, if_pos h2, if_neg hfa, h.fwd]
      rw [digonEmbed_of_eq hn, h2]
    · have hn : EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).facePerm x) =
          S.map.facePerm (EdgeDeletion.value S.map a x) := by
        rw [hv, EdgeDeletion.next_of_ne_of_ne S.map a h1 h2]
      have hn' : EdgeDeletion.value S.map a ((EdgeDeletion.toCombMap S.map a).facePerm x) ≠ b := by
        rw [hn]
        exact fun hb => EdgeDeletion.value_ne S.map a x
          (S.map.facePerm.injective (hb.trans h.fwd.symm))
      rw [digonEmbed_of_ne hn', hn]

/-- **The successor after deleting the edge of a digon**, on the image of `digonRho`. -/
theorem next_digonRho (h : IsDigon S a b rest) {z : S.map.Dart} (hzb : z ≠ b) :
    EdgeDeletion.next S.map a (digonRho S a b z) = digonRho S a b (S.map.facePerm z) := by
  by_cases hza : z = S.map.alpha a
  · subst hza
    rw [digonRho_of_eq, EdgeDeletion.next, if_pos h.bwd]
    by_cases hf : S.map.facePerm (S.map.alpha a) = S.map.alpha a
    · rw [if_pos hf, hf, digonRho_of_eq, h.fwd]
    · rw [if_neg hf, digonRho_of_ne hf]
  · rw [digonRho_of_ne hza]
    have h1 : S.map.facePerm z ≠ a := fun hb =>
      hzb (S.map.facePerm.injective (hb.trans h.bwd.symm))
    by_cases h2 : S.map.facePerm z = S.map.alpha a
    · have hfa : S.map.facePerm a ≠ a := fun ha => h.ne (ha.symm.trans h.fwd)
      rw [EdgeDeletion.next, if_neg h1, if_pos h2, if_neg hfa, h.fwd, h2, digonRho_of_eq]
    · rw [EdgeDeletion.next_of_ne_of_ne S.map a h1 h2, digonRho_of_ne h2]

theorem digonCyc_avoid (h : IsDigon S a b rest) :
    ∀ z ∈ S.cyc.map (digonRho S a b), z ≠ a ∧ z ≠ S.map.alpha a := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  exact ⟨digonRho_ne_a h (fun hwa => h.not_mem_a (by rwa [hwa] at hw)), digonRho_ne_alpha h w⟩

/-- The exterior cycle of the deleted map: the exterior cycle of the stage with `alpha a`
read as `b`. -/
noncomputable def digonCyc (h : IsDigon S a b rest) : List (EdgeDeletion.Dart S.map a) :=
  (EdgeDeletion.exists_map_value_eq S.map a _ (digonCyc_avoid h)).choose

theorem map_value_digonCyc (h : IsDigon S a b rest) :
    (digonCyc h).map (EdgeDeletion.value S.map a) = S.cyc.map (digonRho S a b) :=
  (EdgeDeletion.exists_map_value_eq S.map a _ (digonCyc_avoid h)).choose_spec

theorem isFaceCycle_digonCyc (h : IsDigon S a b rest) :
    (EdgeDeletion.toCombMap S.map a).IsFaceCycle (digonCyc h) := by
  have hc := S.isFaceCycle
  refine EdgeDeletion.isFaceCycle_of_map_value S.map a (map_value_digonCyc h)
    (fun hn => hc.ne_nil (List.map_eq_nil_iff.mp hn))
    (hc.nodup.map_on fun z hz w hw hzw =>
      digonRho_inj (h.ne_b_of_mem hz) (h.ne_b_of_mem hw) hzw) ?_ ?_
  · rw [List.isChain_map]
    exact hc.chain.imp_of_mem_imp fun z w hz _ hzw => by
      have h' : S.map.facePerm z = w := hzw
      show EdgeDeletion.next S.map a (digonRho S a b z) = digonRho S a b w
      rw [next_digonRho h (h.ne_b_of_mem hz), h']
  · intro u hu v hv
    have hu' : (S.cyc.map (digonRho S a b)).getLast? = some u := hu
    have hv' : (S.cyc.map (digonRho S a b)).head? = some v := hv
    rw [List.getLast?_map, List.getLast?_eq_some_getLast hc.ne_nil] at hu'
    rw [List.head?_map, List.head?_eq_some_head hc.ne_nil] at hv'
    rw [← Option.some.inj hu', ← Option.some.inj hv',
      next_digonRho h (h.ne_b_of_mem (List.getLast_mem hc.ne_nil)), hc.closes]

theorem digonEmbed_mem_iff (h : IsDigon S a b rest) (x : EdgeDeletion.Dart S.map a) :
    digonEmbed S a b x ∈ S.cyc ↔ x ∈ digonCyc h := by
  rw [← List.mem_map_of_injective (EdgeDeletion.value_injective S.map a), map_value_digonCyc h,
    List.mem_map, ← digonRho_embed (b := b) x]
  constructor
  · intro hm
    exact ⟨_, hm, rfl⟩
  · rintro ⟨w, hw, hwx⟩
    rwa [digonRho_inj (h.ne_b_of_mem hw) (digonEmbed_ne_b h x) hwx] at hw

theorem rest_digonEmbed_facePerm (h : IsDigon S a b rest) (x : EdgeDeletion.Dart S.map a) :
    rest (digonEmbed S a b ((EdgeDeletion.toCombMap S.map a).facePerm x)) ↔
      rest (digonEmbed S a b x) := by
  rw [digonEmbed_facePerm h x]
  exact h.rest_facePerm _

theorem digonEmbed_good (h : IsDigon S a b rest) (x : EdgeDeletion.Dart S.map a)
    (hr : ¬ rest (digonEmbed S a b x)) : ¬ S.bad (digonEmbed S a b x) := fun hb => by
  rcases h.bad_imp _ hb with h1 | h1 | h1
  · exact digonEmbed_ne_a x h1
  · exact digonEmbed_ne_b h x h1
  · exact hr h1

/-- **Deleting a pending digon.**  Delete the edge of `a`; the dart `b` takes the place of
`alpha a` on the face across that edge. -/
noncomputable def deleteDigon (h : IsDigon S a b rest) : FoldStage X where
  map := EdgeDeletion.toCombMap S.map a
  lab := fun x => S.lab (EdgeDeletion.value S.map a x)
  lab_sigma := deletion_lab_sigma S a
  adj := deletion_adj S a
  cyc := digonCyc h
  isFaceCycle := isFaceCycle_digonCyc h
  bad := fun x => rest (digonEmbed S a b x)
  bad_facePerm := rest_digonEmbed_facePerm h
  cyc_bad := fun x hx hr => S.cyc_bad _ ((digonEmbed_mem_iff h x).mpr hx) (h.rest_imp _ hr)
  tri := fun x hx hxb => S.tri_of_embed (N := EdgeDeletion.toCombMap S.map a)
    (fun y => S.lab (EdgeDeletion.value S.map a y)) (isFaceCycle_digonCyc h)
    (fun y => rest (digonEmbed S a b y)) (rest_digonEmbed_facePerm h) (digonEmbed S a b)
    digonEmbed_injective (lab_digonEmbed h) (fun y hy hm => hy ((digonEmbed_mem_iff h y).mp hm))
    (digonEmbed_good h) (fun y _ _ => digonEmbed_facePerm h y) x hx hxb

/-- Deleting a pending digon keeps the boundary. -/
theorem deleteDigon_boundary (h : IsDigon S a b rest) :
    (deleteDigon h).boundary = S.boundary := by
  apply boundary_eq_of_map_lab
  have e1 := congrArg (List.map S.lab) (map_value_digonCyc h)
  have e2 : S.lab ∘ digonRho S a b = S.lab := funext (lab_digonRho h)
  rw [List.map_map, List.map_map, e2] at e1
  exact e1

/-- Deleting a pending digon keeps planarity. -/
theorem deleteDigon_planar (h : IsDigon S a b rest) (hS : S.map.IsPlanar) :
    (deleteDigon h).map.IsPlanar :=
  EdgeDeletion.planar_of_neFace S.map a hS
    (EdgeDeletion.ofValue S.map a b h.ne.symm h.alpha_ne.symm) h.face_ne

/-- Deleting a pending digon removes one face. -/
theorem deleteDigon_faceCount (h : IsDigon S a b rest) (hS : S.map.IsPlanar) :
    (deleteDigon h).map.faceCount + 1 = S.map.faceCount := by
  have hb := EdgeDeletion.faceCount_balance_of_neFace S.map a h.face_ne
  have hv := EdgeDeletion.vertexCount_eq_of_neFace S.map a hS.1
    (EdgeDeletion.ofValue S.map a b h.ne.symm h.alpha_ne.symm) h.face_ne
  show (EdgeDeletion.toCombMap S.map a).faceCount + 1 = S.map.faceCount
  omega

end Digon

end FoldStage

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.FoldStage.tri_of_embed
#audit_axioms GroupApproximation.Systolic.FoldStage.toStage_boundary
#audit_axioms GroupApproximation.Systolic.FoldStage.exists_triangulatedDisc
#audit_axioms GroupApproximation.Systolic.FoldStage.deleteDigon_boundary
#audit_axioms GroupApproximation.Systolic.FoldStage.deleteDigon_planar
#audit_axioms GroupApproximation.Systolic.FoldStage.deleteDigon_faceCount
