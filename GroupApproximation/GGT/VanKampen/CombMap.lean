import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# Finite combinatorial maps

This file defines a finite combinatorial map by a fixed-point-free dart
involution `alpha` and a vertex rotation `sigma`.  Vertices are the orbits of
`sigma`, edges are the two-element orbits of `alpha`, and faces are the orbits
of `sigma * alpha`, where permutation multiplication acts from right to left.

The degree of an orbit is defined as the cardinality of its fibre in the dart
set.  The fibre decomposition proves that the sums of the vertex and face
degrees both equal the number of darts.  A separate two-element-fibre proof
for `alpha` then identifies this number with twice the number of edges.  These
are the incidence identities used in the Euler estimates in Osin's Appendix,
Lemma 9.7 (`Gr0`).
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open Equiv

universe u

/-- The equivalence relation whose classes are the two darts of an edge. -/
def DartPairRel {D : Type u} (alpha : Perm D) (x y : D) : Prop :=
  x = y ∨ alpha x = y

namespace DartPairRel

/-- A fixed-point-free involution gives an equivalence relation on darts. -/
theorem equivalence {D : Type u} (alpha : Perm D)
    (hinv : Function.Involutive alpha) : Equivalence (DartPairRel alpha) := by
  refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
  · intro x y hxy
    rcases hxy with hxy | hxy
    · exact Or.inl hxy.symm
    · right
      rw [← hxy]
      exact hinv x
  · intro x y z hxy hyz
    rcases hxy with hxy | hxy
    · rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · right
        rw [hxy]
        exact hyz
    · rcases hyz with hyz | hyz
      · right
        exact hxy.trans hyz
      · left
        rw [← hyz, ← hxy]
        exact (hinv x).symm

end DartPairRel

/-- A finite orientable combinatorial map in permutation form. -/
structure CombMap where
  /-- Oriented edge-ends. -/
  Dart : Type u
  dartFintype : Fintype Dart
  /-- Reversal of an oriented edge. -/
  alpha : Perm Dart
  /-- Cyclic rotation of darts based at a vertex. -/
  sigma : Perm Dart
  /-- Reversing an edge twice returns the original dart. -/
  alpha_involutive : Function.Involutive alpha
  /-- No dart is its own reverse. -/
  alpha_fixedPointFree : ∀ d, alpha d ≠ d

attribute [instance] CombMap.dartFintype

namespace CombMap

/-- The orbit type of a permutation. -/
abbrev Orbit {D : Type u} (p : Perm D) := Quotient p.SameCycle.setoid

/-- The two-element setoid induced by edge reversal. -/
def edgeSetoid (M : CombMap) : Setoid M.Dart where
  r := DartPairRel M.alpha
  iseqv := DartPairRel.equivalence M.alpha M.alpha_involutive

/-- Vertices are `sigma`-orbits. -/
abbrev Vertex (M : CombMap) := Orbit M.sigma

/-- Edges are `alpha`-pairs. -/
abbrev Edge (M : CombMap) := Quotient M.edgeSetoid

/-- The face rotation.  Lean's permutation multiplication convention gives
`facePerm d = sigma (alpha d)`. -/
def facePerm (M : CombMap) : Perm M.Dart := M.sigma * M.alpha

/-- Faces are orbits of `sigma * alpha`. -/
abbrev Face (M : CombMap) := Orbit M.facePerm

/-- The vertex containing a dart. -/
def vertexOf (M : CombMap) (d : M.Dart) : M.Vertex := Quotient.mk'' d

/-- The edge containing a dart. -/
def edgeOf (M : CombMap) (d : M.Dart) : M.Edge := Quotient.mk'' d

/-- The face containing a dart. -/
def faceOf (M : CombMap) (d : M.Dart) : M.Face := Quotient.mk'' d

/-- Two darts give the same vertex exactly when they are in the same
`sigma`-cycle. -/
theorem vertexOf_eq_iff (M : CombMap) (d e : M.Dart) :
    M.vertexOf d = M.vertexOf e ↔ M.sigma.SameCycle d e :=
  Quotient.eq''

/-- Two darts give the same edge exactly when they are equal or reverses. -/
theorem edgeOf_eq_iff (M : CombMap) (d e : M.Dart) :
    M.edgeOf d = M.edgeOf e ↔ DartPairRel M.alpha d e :=
  Quotient.eq''

/-- Two darts give the same face exactly when they are in the same face
cycle. -/
theorem faceOf_eq_iff (M : CombMap) (d e : M.Dart) :
    M.faceOf d = M.faceOf e ↔ M.facePerm.SameCycle d e :=
  Quotient.eq''

/-- Vertex rotation preserves the vertex of a dart. -/
theorem vertexOf_sigma (M : CombMap) (d : M.Dart) :
    M.vertexOf (M.sigma d) = M.vertexOf d := by
  rw [M.vertexOf_eq_iff]
  exact Equiv.Perm.SameCycle.apply_left Equiv.Perm.SameCycle.rfl

/-- Edge reversal preserves the edge of a dart. -/
theorem edgeOf_alpha (M : CombMap) (d : M.Dart) :
    M.edgeOf (M.alpha d) = M.edgeOf d := by
  rw [M.edgeOf_eq_iff]
  exact Or.inr (M.alpha_involutive d)

/-- Face rotation preserves the face of a dart. -/
theorem faceOf_facePerm (M : CombMap) (d : M.Dart) :
    M.faceOf (M.facePerm d) = M.faceOf d := by
  rw [M.faceOf_eq_iff]
  exact Equiv.Perm.SameCycle.apply_left Equiv.Perm.SameCycle.rfl

/-- Number of darts. -/
def dartCount (M : CombMap) : ℕ := Nat.card M.Dart

/-- Number of vertices. -/
def vertexCount (M : CombMap) : ℕ := Nat.card M.Vertex

/-- Number of edges. -/
def edgeCount (M : CombMap) : ℕ := Nat.card M.Edge

/-- Number of faces. -/
def faceCount (M : CombMap) : ℕ := Nat.card M.Face

/-- Cardinality of an orbit fibre. -/
def orbitDegree {D : Type u} [Finite D] (p : Perm D) (o : Orbit p) : ℕ :=
  Nat.card {d : D // (Quotient.mk'' d : Orbit p) = o}

/-- Degree of a vertex. -/
def vertexDegree (M : CombMap) (v : M.Vertex) : ℕ :=
  orbitDegree M.sigma v

/-- Degree of an edge. -/
def edgeDegree (M : CombMap) (e : M.Edge) : ℕ :=
  Nat.card {d : M.Dart // M.edgeOf d = e}

/-- Degree of a face. -/
def faceDegree (M : CombMap) (f : M.Face) : ℕ :=
  orbitDegree M.facePerm f

/-- Orbit fibres partition the underlying finite type. -/
theorem sum_orbitDegree {D : Type u} [Fintype D] (p : Perm D) :
    ∑ o : Orbit p, orbitDegree p o = Nat.card D := by
  classical
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv
    (fun d : D => (Quotient.mk'' d : Orbit p)))

/-- The sum of vertex degrees is the number of darts. -/
theorem sum_vertexDegree_eq_dartCount (M : CombMap) :
    ∑ v : M.Vertex, M.vertexDegree v = M.dartCount := by
  exact sum_orbitDegree M.sigma

/-- The sum of face degrees is the number of darts. -/
theorem sum_faceDegree_eq_dartCount (M : CombMap) :
    ∑ f : M.Face, M.faceDegree f = M.dartCount := by
  exact sum_orbitDegree M.facePerm

/-- The fibre over an edge represented by `d` has exactly the two darts `d`
and `alpha d`. -/
theorem edgeDegree_mk (M : CombMap) (d : M.Dart) :
    M.edgeDegree (M.edgeOf d) = 2 := by
  apply Nat.card_eq_two_iff.mpr
  let x : {e : M.Dart // M.edgeOf e = M.edgeOf d} := ⟨d, rfl⟩
  let y : {e : M.Dart // M.edgeOf e = M.edgeOf d} :=
    ⟨M.alpha d, M.edgeOf_alpha d⟩
  refine ⟨x, y, ?_, ?_⟩
  · intro hxy
    apply M.alpha_fixedPointFree d
    have hval : d = M.alpha d := congrArg Subtype.val hxy
    exact hval.symm
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hz : DartPairRel M.alpha z.1 d :=
      (M.edgeOf_eq_iff z.1 d).mp z.2
    rcases hz with hz | hz
    · left
      exact Subtype.ext hz
    · right
      apply Subtype.ext
      have halpha := congrArg M.alpha hz
      rw [M.alpha_involutive z.1] at halpha
      exact halpha

/-- Every edge has degree two. -/
theorem edgeDegree_eq_two (M : CombMap) (e : M.Edge) :
    M.edgeDegree e = 2 := by
  refine Quotient.inductionOn' e ?_
  intro d
  exact M.edgeDegree_mk d

/-- The dart set has twice as many elements as the edge set. -/
theorem dartCount_eq_two_mul_edgeCount (M : CombMap) :
    M.dartCount = 2 * M.edgeCount := by
  classical
  calc
    M.dartCount = Nat.card
        (Σ e : M.Edge, {d : M.Dart // M.edgeOf d = e}) := by
      exact Nat.card_congr (Equiv.sigmaFiberEquiv M.edgeOf).symm
    _ = ∑ e : M.Edge, M.edgeDegree e := by
      rw [Nat.card_sigma]
      rfl
    _ = 2 * M.edgeCount := by
      simp only [M.edgeDegree_eq_two, Finset.sum_const, Finset.card_univ,
        Nat.nsmul_eq_mul, M.edgeCount, Nat.card_eq_fintype_card, Nat.mul_comm]

/-- The sum of vertex degrees equals twice the number of edges. -/
theorem sum_vertexDegree_eq_two_mul_edgeCount (M : CombMap) :
    ∑ v : M.Vertex, M.vertexDegree v = 2 * M.edgeCount := by
  rw [M.sum_vertexDegree_eq_dartCount, M.dartCount_eq_two_mul_edgeCount]

/-- The sum of face degrees equals twice the number of edges. -/
theorem sum_faceDegree_eq_two_mul_edgeCount (M : CombMap) :
    ∑ f : M.Face, M.faceDegree f = 2 * M.edgeCount := by
  rw [M.sum_faceDegree_eq_dartCount, M.dartCount_eq_two_mul_edgeCount]

/-- Two darts are adjacent when one is obtained from the other by an edge
reversal or one vertex rotation. -/
def Adjacent (M : CombMap) (d e : M.Dart) : Prop :=
  M.alpha d = e ∨ M.sigma d = e

/-- A map is connected when the equivalence closure of its elementary dart
moves has one class. -/
def IsConnected (M : CombMap) : Prop :=
  ∀ d e : M.Dart, Relation.EqvGen M.Adjacent d e

/-- Euler characteristic of the closed combinatorial surface. -/
def eulerCharacteristic (M : CombMap) : ℤ :=
  (M.vertexCount : ℤ) - (M.edgeCount : ℤ) + (M.faceCount : ℤ)

/-- A connected combinatorial map is planar when its Euler characteristic is
two. -/
def IsPlanar (M : CombMap) : Prop :=
  M.IsConnected ∧ M.eulerCharacteristic = 2

/-- Planarity exposes the Euler formula in cardinal form. -/
theorem euler_eq_two (M : CombMap) (hM : M.IsPlanar) :
    (M.vertexCount : ℤ) - (M.edgeCount : ℤ) + (M.faceCount : ℤ) = 2 :=
  hM.2

/-- Planarity includes connectedness. -/
theorem connected_of_planar (M : CombMap) (hM : M.IsPlanar) : M.IsConnected :=
  hM.1

/-- Euler's curvature consequence: if every face of a planar map has degree
at least three, some vertex has degree at most five.  This is the local
deletion step behind Osin's five-owner orientation of the estimating graph. -/
theorem exists_vertexDegree_le_five_of_faceDegree_ge_three
    (M : CombMap) (hM : M.IsPlanar)
    (hface : ∀ f : M.Face, 3 ≤ M.faceDegree f) :
    ∃ v : M.Vertex, M.vertexDegree v ≤ 5 := by
  classical
  have hEulerInt : (M.vertexCount : ℤ) + (M.faceCount : ℤ) =
      (M.edgeCount : ℤ) + 2 := by
    have h := M.euler_eq_two hM
    linarith
  have hEuler : M.vertexCount + M.faceCount = M.edgeCount + 2 := by
    exact_mod_cast hEulerInt
  have hfaceSum : 3 * M.faceCount ≤ 2 * M.edgeCount := by
    calc
      3 * M.faceCount = ∑ _f : M.Face, 3 := by
        simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
          M.faceCount, Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ ∑ f : M.Face, M.faceDegree f := by
        apply Finset.sum_le_sum
        intro f _
        exact hface f
      _ = 2 * M.edgeCount := M.sum_faceDegree_eq_two_mul_edgeCount
  by_contra hsmall
  have hvertex : ∀ v : M.Vertex, 6 ≤ M.vertexDegree v := by
    intro v
    have hnot : ¬ M.vertexDegree v ≤ 5 := by
      intro hv
      exact hsmall ⟨v, hv⟩
    omega
  have hvertexSum : 6 * M.vertexCount ≤ 2 * M.edgeCount := by
    calc
      6 * M.vertexCount = ∑ _v : M.Vertex, 6 := by
        simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
          M.vertexCount, Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ ∑ v : M.Vertex, M.vertexDegree v := by
        apply Finset.sum_le_sum
        intro v _
        exact hvertex v
      _ = 2 * M.edgeCount := M.sum_vertexDegree_eq_two_mul_edgeCount
  omega

end CombMap

end VanKampen
end GGT
end GroupApproximation
