import GroupApproximation.GGT.SystolicDisc
import GroupApproximation.GGT.VanKampen.SingleEdgeDisc

/-!
# Filling closed edge paths by triangulated discs

HC2 and HC4 of the minimal-disc layer (`GGT/SystolicDisc.lean`).

* `TriangulatedDisc.oneEdge`: an edge `u v` of `X` bounds the one-edge disc reading
  `[u, v, u]`.
* `fillingStatement_of_simplyConnected`: in a simply connected triangle complex, every
  nonconstant closed edge path bounds a triangulated disc, given the four boundary
  constructors of HC3.  The property "bounds a disc, or is a single vertex" is invariant
  under each triangle move in both directions: a backtrack is removed by zipping and
  created by a pendant edge, a triangle shortcut by inserting a chord and undone by
  attaching a triangle.  So it is invariant under the equivalence the moves generate, and
  the constant path has it.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route (hyperbolicity of `GHB(7)`); certifies no manuscript step on its
own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen

universe u

variable {V : Type u}

namespace TriangulatedDisc

/-- The vertex labelling of the one-edge map: the tail of `false` is `u`, of `true` is `v`. -/
def oneEdgeVtx (u v : V) : SingleEdgeDisc.map.Vertex → V :=
  Quotient.lift (fun b : Bool => cond b v u) (fun a b hab => by
    rw [Equiv.Perm.sameCycle_one.mp hab])

theorem singleEdge_faceDegree (f : SingleEdgeDisc.map.Face) :
    SingleEdgeDisc.map.faceDegree f = 2 :=
  (SingleEdgeDisc.faceBoundary f).length_eq_degree.symm

/-- **HC2: the one-edge disc.**  An edge `u v` of `X` bounds the disc reading `[u, v, u]`. -/
def oneEdge {X : TriangleComplex V} {u v : V} (h : X.G.Adj u v) :
    TriangulatedDisc X [u, v, u] where
  map := SingleEdgeDisc.map
  planar := SingleEdgeDisc.planar_map
  outer := SingleEdgeDisc.map.faceOf false
  vtx := oneEdgeVtx u v
  adj := fun d => by
    cases d
    · exact h
    · exact h.symm
  tri := fun _ hd => absurd (SingleEdgeDisc.faceSubsingleton.allEq _ _) hd
  base := false
  base_outer := rfl
  boundary := by
    have hdeg : SingleEdgeDisc.map.faceDegree (SingleEdgeDisc.map.faceOf false) = 2 :=
      singleEdge_faceDegree _
    apply List.ext_getElem
    · simp only [List.length_ofFn, hdeg, List.length_cons, List.length_nil]
    · intro i _ h2
      rw [List.getElem_ofFn]
      have hi : i < 3 := h2
      interval_cases i
      · show oneEdgeVtx u v
          (SingleEdgeDisc.map.vertexOf ((SingleEdgeDisc.map.facePerm ^ 0) false)) = u
        rw [pow_zero, Equiv.Perm.one_apply]
        rfl
      · show oneEdgeVtx u v
          (SingleEdgeDisc.map.vertexOf ((SingleEdgeDisc.map.facePerm ^ 1) false)) = v
        rw [pow_one]
        rfl
      · show oneEdgeVtx u v
          (SingleEdgeDisc.map.vertexOf ((SingleEdgeDisc.map.facePerm ^ 2) false)) = u
        rw [perm_pow_two_apply]
        rfl

end TriangulatedDisc

variable {X : TriangleComplex V}

/-- A triangle move preserves "bounds a disc, or is a single vertex", in both
directions. -/
theorem fill_iff_of_triangleMove (ha : AttachTriangleStatement X)
    (hb : InsertChordStatement X) (hc : AttachPendantStatement X) (hd : ZipSpurStatement X)
    {x y : List V} (hxy : TriangleMove X x y) :
    (x.length = 1 ∨ Nonempty (TriangulatedDisc X x)) ↔
      (y.length = 1 ∨ Nonempty (TriangulatedDisc X y)) := by
  cases hxy with
  | backtrack p q u v huv =>
    constructor
    · rintro (hlen | ⟨D⟩)
      · exfalso
        simp only [List.length_append, List.length_cons] at hlen
        omega
      · rcases hd p q u v D with h | h
        · exact Or.inr h
        · exact Or.inl (by simp [h])
    · rintro (hlen | ⟨D⟩)
      · simp only [List.length_append, List.length_cons] at hlen
        have hp : p = [] := List.length_eq_zero_iff.mp (by omega)
        have hq : q = [] := List.length_eq_zero_iff.mp (by omega)
        subst hp
        subst hq
        exact Or.inr ⟨TriangulatedDisc.oneEdge huv⟩
      · exact Or.inr (hc p q u v huv D)
  | triangle p q u v w htri =>
    constructor
    · rintro (hlen | ⟨D⟩)
      · exfalso
        simp only [List.length_append, List.length_cons] at hlen
        omega
      · exact Or.inr (hb p q u v w htri D)
    · rintro (hlen | ⟨D⟩)
      · exfalso
        simp only [List.length_append, List.length_cons] at hlen
        omega
      · exact Or.inr (ha p q u v w htri D)

/-- **HC4: filling.**  In a simply connected triangle complex with the four boundary
constructors, every nonconstant closed edge path bounds a triangulated disc. -/
theorem fillingStatement_of_simplyConnected (hsc : SimplyConnected X)
    (ha : AttachTriangleStatement X) (hb : InsertChordStatement X)
    (hc : AttachPendantStatement X) (hd : ZipSpurStatement X) : FillingStatement X := by
  have hEqv : ∀ x y, Relation.EqvGen (TriangleMove X) x y →
      ((x.length = 1 ∨ Nonempty (TriangulatedDisc X x)) ↔
        (y.length = 1 ∨ Nonempty (TriangulatedDisc X y))) := by
    intro x y h
    induction h with
    | rel x y hxy => exact fill_iff_of_triangleMove ha hb hc hd hxy
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  intro v l hl _
  rcases (hEqv _ _ (hsc v l hl)).mpr (Or.inl rfl) with hlen | hD
  · exfalso
    simp only [List.cons_append, List.length_cons, List.length_append,
      List.length_singleton] at hlen
    omega
  · exact hD

/-- **HC10, closed form over the producers of HC3 and HC6.** -/
theorem exists_leastDisc_typedLinks_of_simplyConnected (hsc : SimplyConnected X)
    (ha : AttachTriangleStatement X) (hb : InsertChordStatement X)
    (hc : AttachPendantStatement X) (hd : ZipSpurStatement X)
    (hfold : MirrorFoldStatement X) {n : V → ℕ} (hL : LinksLargeAt X n) {v : V} {l : List V}
    (hl : List.IsChain X.G.Adj (v :: l ++ [v])) (hne : l ≠ []) :
    ∃ D : TriangulatedDisc X (v :: l ++ [v]),
      (∀ D' : TriangulatedDisc X (v :: l ++ [v]), D.innerFaceCount ≤ D'.innerFaceCount) ∧
      ∀ w : D.map.Vertex, D.Interior w → n (D.vtx w) ≤ D.map.vertexDegree w :=
  exists_leastDisc_typedLinks (fillingStatement_of_simplyConnected hsc ha hb hc hd) hfold hL hl
    hne

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms TriangulatedDisc.oneEdge
#audit_axioms fillingStatement_of_simplyConnected
#audit_axioms exists_leastDisc_typedLinks_of_simplyConnected
