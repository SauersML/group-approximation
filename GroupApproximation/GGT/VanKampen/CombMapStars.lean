import GroupApproximation.GGT.VanKampen.CactusBoundary
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Union
import Mathlib.Data.ZMod.Basic

/-!
# Corners, face stars, and closed planar combinatorial maps

This module supplies the permutation-map operations used by the successive-star
argument for girth-eight triangular presentations.  A corner is a position in a
`sigma` orbit together with the faces on its two sides.  The closed star of a
face consists of all faces meeting it at a vertex, and `starLayer` takes the
successive disjoint differences of those closed stars.  Boundary prefixes are
literal sublists of the stored outer traversal.  Finally, `SphericalCombMap`
is the closed planar-map type, with no distinguished exterior face.

The six-dart model at the end has one three-cycle in each orientation.  It is
the local one-triangle test for the corner and face-rotation conventions.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open Equiv

universe u w v

/-! ## Corners and cyclic vertex orbits -/

/-- A corner at a map vertex, represented by its outgoing dart. -/
structure Corner (M : CombMap.{u}) (vertex : M.Vertex) where
  /-- The outgoing dart at the corner. -/
  dart : M.Dart
  /-- The dart belongs to the specified vertex orbit. -/
  atVertex : M.vertexOf dart = vertex

namespace Corner

variable {M : CombMap.{u}} {vertex : M.Vertex}

/-- The face on the dart side of a corner. -/
def firstFace (c : Corner M vertex) : M.Face :=
  M.faceOf c.dart

/-- The face on the reverse-dart side of a corner. -/
def secondFace (c : Corner M vertex) : M.Face :=
  M.faceOf (M.alpha c.dart)

/-- Rotate a corner once around its vertex. -/
def rotate (c : Corner M vertex) : Corner M vertex where
  dart := M.sigma c.dart
  atVertex := (M.vertexOf_sigma c.dart).trans c.atVertex

@[simp]
theorem rotate_dart (c : Corner M vertex) : c.rotate.dart = M.sigma c.dart :=
  rfl

end Corner

namespace CombMap

/-- The representative selected by the quotient implementation of a vertex. -/
noncomputable def vertexRepresentative (M : CombMap.{u}) (vertex : M.Vertex) :
    M.Dart :=
  Quotient.out vertex

/-- The selected dart represents the vertex from which it was chosen. -/
theorem vertexOf_vertexRepresentative (M : CombMap.{u}) (vertex : M.Vertex) :
    M.vertexOf (M.vertexRepresentative vertex) = vertex :=
  Quotient.out_eq vertex

/-- Iterating the vertex rotation from the selected representative. -/
noncomputable def vertexOrbitDart (M : CombMap.{u}) (vertex : M.Vertex)
    (i : ℕ) : M.Dart :=
  (M.sigma ^ i) (M.vertexRepresentative vertex)

/-- Successive orbit darts follow `sigma`. -/
theorem vertexOrbitDart_succ (M : CombMap.{u}) (vertex : M.Vertex) (i : ℕ) :
    M.vertexOrbitDart vertex (i + 1) =
      M.sigma (M.vertexOrbitDart vertex i) := by
  rw [vertexOrbitDart, vertexOrbitDart, pow_succ', Perm.mul_apply]

/-- A full orbit-degree rotation returns to the selected dart. -/
theorem pow_orbitDegree_apply (M : CombMap.{u}) (d : M.Dart) :
    (M.sigma ^ orbitDegree M.sigma (Quotient.mk'' d)) d = d := by
  classical
  by_cases hd : M.sigma d = d
  · have hdegree : orbitDegree M.sigma (Quotient.mk'' d) = 1 := by
      rw [← closedOrbitList.length_eq_orbitDegree M.sigma d]
      simp [closedOrbitList, hd]
    rw [hdegree, pow_one, hd]
  · have hdegree : orbitDegree M.sigma (Quotient.mk'' d) =
        (M.sigma.cycleOf d).support.card := by
      rw [← closedOrbitList.length_eq_orbitDegree M.sigma d]
      simp [closedOrbitList, hd, Equiv.Perm.length_toList]
    rw [hdegree]
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply
      M.sigma (M.sigma.cycleOf d).support.card d
    simpa using hmod.symm

/-- A full vertex-degree rotation is periodic at every later position. -/
theorem vertexOrbitDart_periodic (M : CombMap.{u}) (vertex : M.Vertex)
    (i : ℕ) :
    M.vertexOrbitDart vertex (i + M.vertexDegree vertex) =
      M.vertexOrbitDart vertex i := by
  let d := M.vertexRepresentative vertex
  have hvertex : (Quotient.mk'' d : M.Vertex) = vertex :=
    M.vertexOf_vertexRepresentative vertex
  have hperiod : (M.sigma ^ M.vertexDegree vertex) d = d := by
    rw [← hvertex]
    exact M.pow_orbitDegree_apply d
  rw [vertexOrbitDart, vertexOrbitDart, pow_add, Perm.mul_apply, hperiod]

/-- Every dart of a vertex occurs before the first vertex-degree return. -/
theorem exists_vertexOrbitDart (M : CombMap.{u}) (vertex : M.Vertex)
    (e : M.Dart) (he : M.vertexOf e = vertex) :
    ∃ i, i < M.vertexDegree vertex ∧ M.vertexOrbitDart vertex i = e := by
  classical
  let d := M.vertexRepresentative vertex
  have hdvertex : M.vertexOf d = vertex :=
    M.vertexOf_vertexRepresentative vertex
  have hcycle : M.sigma.SameCycle d e := by
    rw [← M.vertexOf_eq_iff d e]
    exact hdvertex.trans he.symm
  by_cases hd : M.sigma d = d
  · have heq : d = e := hcycle.eq_of_left hd
    have hdegree : M.vertexDegree vertex = 1 := by
      rw [← hdvertex]
      change orbitDegree M.sigma (Quotient.mk'' d) = 1
      rw [← closedOrbitList.length_eq_orbitDegree M.sigma d]
      simp [closedOrbitList, hd]
    refine ⟨0, by omega, ?_⟩
    rw [vertexOrbitDart, pow_zero, Perm.one_apply]
    change d = e
    exact heq
  · have hdmem : d ∈ M.sigma.support := by
      simpa [Equiv.Perm.mem_support] using hd
    obtain ⟨i, hi, hie⟩ := hcycle.exists_pow_eq_of_mem_support hdmem
    have hdegree : M.vertexDegree vertex =
        (M.sigma.cycleOf d).support.card := by
      rw [← hdvertex]
      change orbitDegree M.sigma (Quotient.mk'' d) = _
      rw [← closedOrbitList.length_eq_orbitDegree M.sigma d]
      simp [closedOrbitList, hd, Equiv.Perm.length_toList]
    exact ⟨i, hdegree ▸ hi, hie⟩

/-- Every vertex orbit contains its selected representative, so its degree is
strictly positive. -/
theorem vertexDegree_pos (M : CombMap.{u}) (vertex : M.Vertex) :
    0 < M.vertexDegree vertex := by
  obtain ⟨i, hi, _⟩ := M.exists_vertexOrbitDart vertex
    (M.vertexRepresentative vertex) (M.vertexOf_vertexRepresentative vertex)
  omega

/-- Orbit positions before the vertex degree are distinct. -/
theorem vertexOrbitDart_injective (M : CombMap.{u}) (vertex : M.Vertex)
    (i j : ℕ) (hi : i < M.vertexDegree vertex)
    (hj : j < M.vertexDegree vertex)
    (hij : M.vertexOrbitDart vertex i = M.vertexOrbitDart vertex j) :
    i = j := by
  classical
  let d := M.vertexRepresentative vertex
  have hdvertex : M.vertexOf d = vertex :=
    M.vertexOf_vertexRepresentative vertex
  by_cases hd : M.sigma d = d
  · have hdegree : M.vertexDegree vertex = 1 := by
      rw [← hdvertex]
      change orbitDegree M.sigma (Quotient.mk'' d) = 1
      rw [← closedOrbitList.length_eq_orbitDegree M.sigma d]
      simp [closedOrbitList, hd]
    omega
  · let l := M.sigma.toList d
    have hlength : l.length = M.vertexDegree vertex := by
      rw [← hdvertex]
      change l.length = orbitDegree M.sigma (Quotient.mk'' d)
      rw [← closedOrbitList.length_eq_orbitDegree M.sigma d]
      simp [l, closedOrbitList, hd]
    have hget : l[i] = l[j] := by
      have hi' : i < l.length := by rw [hlength]; exact hi
      have hj' : j < l.length := by rw [hlength]; exact hj
      change (M.sigma.toList d)[i] = (M.sigma.toList d)[j]
      rw [Equiv.Perm.getElem_toList M.sigma d i hi',
        Equiv.Perm.getElem_toList M.sigma d j hj']
      exact hij
    exact (Equiv.Perm.nodup_toList M.sigma d).getElem_inj_iff.mp hget

/-! ## Face stars -/

/-- Two faces meet when they contain darts based at the same vertex. -/
def FaceMeets (M : CombMap.{u}) (f g : M.Face) : Prop :=
  ∃ d e : M.Dart,
    M.faceOf d = f ∧ M.faceOf e = g ∧ M.vertexOf d = M.vertexOf e

theorem faceMeets_refl (M : CombMap.{u}) (f : M.Face) : M.FaceMeets f f := by
  refine Quotient.inductionOn' f ?_
  intro d
  exact ⟨d, d, rfl, rfl, rfl⟩

theorem faceMeets_symm (M : CombMap.{u}) {f g : M.Face}
    (h : M.FaceMeets f g) : M.FaceMeets g f := by
  obtain ⟨d, e, hdf, heg, hv⟩ := h
  exact ⟨e, d, heg, hdf, hv.symm⟩

/-- The closed star of one face: all faces meeting it at a vertex. -/
noncomputable def faceStar (M : CombMap.{u}) (f : M.Face) : Finset M.Face := by
  classical
  exact Finset.univ.filter (M.FaceMeets f)

theorem mem_faceStar_iff (M : CombMap.{u}) (f g : M.Face) :
    g ∈ M.faceStar f ↔ M.FaceMeets f g := by
  classical
  simp [faceStar]

theorem mem_faceStar_self (M : CombMap.{u}) (f : M.Face) :
    f ∈ M.faceStar f :=
  (M.mem_faceStar_iff f f).mpr (M.faceMeets_refl f)

/-- Apply the closed-star operation to every face in a finite set. -/
noncomputable def faceStarSet (M : CombMap.{u}) (faces : Finset M.Face) :
    Finset M.Face := by
  classical
  exact faces.biUnion M.faceStar

theorem faceStarSet_mono (M : CombMap.{u}) {s t : Finset M.Face}
    (hst : s ⊆ t) : M.faceStarSet s ⊆ M.faceStarSet t := by
  classical
  intro f hf
  rw [faceStarSet, Finset.mem_biUnion] at hf
  obtain ⟨g, hgs, hfg⟩ := hf
  rw [faceStarSet, Finset.mem_biUnion]
  exact ⟨g, hst hgs, hfg⟩

theorem subset_faceStarSet (M : CombMap.{u}) (s : Finset M.Face) :
    s ⊆ M.faceStarSet s := by
  classical
  intro f hf
  rw [faceStarSet, Finset.mem_biUnion]
  exact ⟨f, hf, M.mem_faceStar_self f⟩

/-- Faces reached after at most `n` successive closed-star expansions. -/
noncomputable def faceStarBall (M : CombMap.{u}) (seed : Finset M.Face) :
    ℕ → Finset M.Face
  | 0 => seed
  | n + 1 => M.faceStarSet (M.faceStarBall seed n)

/-- The new faces first reached at the `n`-th star expansion. -/
noncomputable def faceStarLayer (M : CombMap.{u}) (seed : Finset M.Face) :
    ℕ → Finset M.Face := fun n ↦ by
  classical
  exact if n = 0 then seed
    else M.faceStarBall seed n \ M.faceStarBall seed (n - 1)

theorem faceStarBall_mono_succ (M : CombMap.{u}) (seed : Finset M.Face)
    (n : ℕ) : M.faceStarBall seed n ⊆ M.faceStarBall seed (n + 1) := by
  change M.faceStarBall seed n ⊆ M.faceStarSet (M.faceStarBall seed n)
  exact M.subset_faceStarSet _

/-- Closed star balls are monotone in their radius. -/
theorem faceStarBall_mono (M : CombMap.{u}) (seed : Finset M.Face)
    {i j : ℕ} (hij : i ≤ j) :
    M.faceStarBall seed i ⊆ M.faceStarBall seed j := by
  induction j, hij using Nat.le_induction with
  | base => exact fun _ h ↦ h
  | succ j _ ih =>
      exact ih.trans (M.faceStarBall_mono_succ seed j)

/-- A star layer is contained in the ball at the same radius. -/
theorem faceStarLayer_subset_ball (M : CombMap.{u})
    (seed : Finset M.Face) (n : ℕ) :
    M.faceStarLayer seed n ⊆ M.faceStarBall seed n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [faceStarLayer]
  · rw [faceStarLayer, if_neg hn]
    exact Finset.sdiff_subset

theorem faceStarLayer_succ_disjoint_ball (M : CombMap.{u})
    (seed : Finset M.Face) (n : ℕ) :
    Disjoint (M.faceStarLayer seed (n + 1)) (M.faceStarBall seed n) := by
  classical
  rw [faceStarLayer, if_neg (by omega)]
  have hpred : n + 1 - 1 = n := by omega
  rw [hpred]
  change Disjoint
    (M.faceStarBall seed (n + 1) \ M.faceStarBall seed n)
    (M.faceStarBall seed n)
  exact Finset.sdiff_disjoint

/-- Layers at two different radii are disjoint. -/
theorem faceStarLayer_disjoint (M : CombMap.{u})
    (seed : Finset M.Face) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (M.faceStarLayer seed i) (M.faceStarLayer seed j) := by
  classical
  wlog hlt : i < j generalizing i j with H
  · exact (H M seed hij.symm (by omega)).symm
  have hjpos : j ≠ 0 := by omega
  rw [Finset.disjoint_left]
  intro f hfi hfj
  have hfiBall : f ∈ M.faceStarBall seed i :=
    M.faceStarLayer_subset_ball seed i hfi
  have hijpred : i ≤ j - 1 := by omega
  have hfpred : f ∈ M.faceStarBall seed (j - 1) :=
    M.faceStarBall_mono seed hijpred hfiBall
  rw [faceStarLayer, if_neg hjpos] at hfj
  exact hfj.2 hfpred

/-- Pairwise-disjoint star layers contained in a finite face set have total
cardinality at most the cardinality of that set.  This is the exact counting
part of the successive-star estimate; the geometric covering lower bound is
separate. -/
theorem sum_faceStarLayer_card_le (M : CombMap.{u})
    (seed container : Finset M.Face) (m : ℕ)
    (hsub : ∀ i : Fin m, M.faceStarLayer seed i ⊆ container) :
    (∑ i : Fin m, (M.faceStarLayer seed i).card) ≤ container.card := by
  classical
  have hpairwise : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i ↦ M.faceStarLayer seed i) := by
    intro i _hi j _hj hij
    exact M.faceStarLayer_disjoint seed (by
      intro hval
      apply hij
      exact Fin.ext hval)
  rw [← Finset.card_biUnion hpairwise]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨i, _hi, hfi⟩ := Finset.mem_biUnion.mp hf
  exact hsub i hfi

end CombMap

/-! ## Literal outer-boundary subpaths -/

/-- A literal subpath of the stored outer-face traversal. -/
structure OuterBoundarySubpath
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (Delta : DiscDiagram.{u, w, v} W) where
  /-- Darts in traversal order. -/
  darts : List Delta.toCombMap.Dart
  /-- Darts before the selected occurrence. -/
  beforeDarts : List Delta.toCombMap.Dart
  /-- Darts after the selected occurrence. -/
  afterDarts : List Delta.toCombMap.Dart
  /-- The selected occurrence is a literal list split. -/
  split : (Delta.faceBoundary Delta.outerFace).darts =
    beforeDarts ++ darts ++ afterDarts
  /-- Consecutive selected darts follow the outer face permutation. -/
  chain : darts.IsChain fun d e ↦ Delta.toCombMap.facePerm d = e

/-- The first `n` darts of the outer traversal form a boundary subpath. -/
def boundaryPrefix
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (Delta : DiscDiagram.{u, w, v} W)
    (n : ℕ) : OuterBoundarySubpath Delta where
  darts := (Delta.faceBoundary Delta.outerFace).darts.take n
  beforeDarts := []
  afterDarts := (Delta.faceBoundary Delta.outerFace).darts.drop n
  split := by simp [List.take_append_drop]
  chain := (Delta.faceBoundary Delta.outerFace).chain.take n

@[simp]
theorem boundaryPrefix_darts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (Delta : DiscDiagram.{u, w, v} W)
    (n : ℕ) :
    (boundaryPrefix Delta n).darts =
      (Delta.faceBoundary Delta.outerFace).darts.take n :=
  rfl

/-! ## Closed planar maps -/

/-- A combinatorial two-sphere without a distinguished exterior face. -/
structure SphericalCombMap where
  /-- The closed rotation system. -/
  toCombMap : CombMap.{u}
  /-- The rotation system is connected and has Euler characteristic two. -/
  planar : toCombMap.IsPlanar

namespace SphericalCombMap

/-- Forget the distinguished exterior face of a disc diagram. -/
def ofDiscDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : SphericalCombMap where
  toCombMap := Delta.toCombMap
  planar := Delta.planar

end SphericalCombMap

/-! ## The one-triangle rotation model -/

/-- Darts of the one-triangle model, separated by orientation. -/
abbrev OneTriangleDart := ZMod 3 × Bool

/-- Edge reversal in the one-triangle model. -/
def oneTriangleAlpha : Perm OneTriangleDart where
  toFun
    | (i, false) => (i, true)
    | (i, true) => (i, false)
  invFun
    | (i, false) => (i, true)
    | (i, true) => (i, false)
  left_inv := by rintro ⟨i, b⟩; cases b <;> rfl
  right_inv := by rintro ⟨i, b⟩; cases b <;> rfl

/-- Vertex rotation pairs the incoming and outgoing darts at each vertex. -/
def oneTriangleSigma : Perm OneTriangleDart where
  toFun
    | (i, false) => (i - 1, true)
    | (i, true) => (i + 1, false)
  invFun
    | (i, false) => (i - 1, true)
    | (i, true) => (i + 1, false)
  left_inv := by
    rintro ⟨i, b⟩
    cases b <;> simp
  right_inv := by
    rintro ⟨i, b⟩
    cases b <;> simp

/-- The closed six-dart map of one triangular 2-cell and its exterior. -/
def oneTriangleCombMap : CombMap where
  Dart := OneTriangleDart
  dartFintype := inferInstance
  alpha := oneTriangleAlpha
  sigma := oneTriangleSigma
  alpha_involutive := by rintro ⟨i, b⟩; cases b <;> rfl
  alpha_fixedPointFree := by rintro ⟨i, b⟩; cases b <;> simp [oneTriangleAlpha]

/-- The positive orientation advances once around the triangle. -/
theorem oneTriangle_facePerm_false (i : ZMod 3) :
    oneTriangleCombMap.facePerm (i, false) = (i + 1, false) :=
  rfl

/-- The reverse orientation runs around the exterior in the opposite order. -/
theorem oneTriangle_facePerm_true (i : ZMod 3) :
    oneTriangleCombMap.facePerm (i, true) = (i - 1, true) :=
  rfl

/-- The two sides of a model corner are the two oriented triangle faces. -/
theorem oneTriangle_corner_incidence (i : ZMod 3) :
    oneTriangleCombMap.faceOf (oneTriangleCombMap.alpha (i, false)) =
      oneTriangleCombMap.faceOf (i, true) :=
  rfl

end VanKampen
end GGT
end GroupApproximation
