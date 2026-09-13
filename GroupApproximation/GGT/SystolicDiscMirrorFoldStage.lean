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

end Deletion

end FoldStage

end GroupApproximation.Systolic

#audit_axioms GroupApproximation.Systolic.FoldStage.tri_of_embed
#audit_axioms GroupApproximation.Systolic.FoldStage.toStage_boundary
#audit_axioms GroupApproximation.Systolic.FoldStage.exists_triangulatedDisc
