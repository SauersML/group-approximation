import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Logic.Relation
import GroupApproximation.Meta.AxiomGuard

/-!
# The Ã₂ lattice building over a principal ideal domain: interface (Z1-base, piece Z.2/Z.4)

This file fixes the shared vocabulary of the Z1-base route (board `k2-poly.md`, modules Z.1–Z.6).
It has no proofs beyond the equivalence relation. It states `BuildingSimplyConnectedStatement`,
which lane k2-bt-sc proves (piece Z.4).

Let `A` be a commutative ring, `B` an `A`-algebra, and `p : A`. In the application `A` is a PID,
`p` is a prime of `A`, and `B = A[1/p]`.
* `latOf g`: the `A`-lattice of `B³` spanned by the columns of `g ∈ GL₃(B)`.
* `Homothetic g h`: `p^a • latOf g = p^b • latOf h` for some `a b : ℕ`.
* `Vertex`: `GL₃(B)` modulo homothety. These are the homothety classes of lattices.
* `buildingGraph`: two distinct vertices are adjacent when they have representatives
  `p • L < L' < L`, in one order or the other.
* `TriStep` and `TriSimplyConnected`: combinatorial simple connectivity of the clique 2-complex
  of a simple graph. Closed edge paths are vertex lists. The moves are:
  - cancel a backtrack `u v u ↦ u`;
  - push an edge across a triangle `u v w ↦ u w`;
  - either move in reverse.

For `A` a PID and `p` prime, `buildingGraph` is the 1-skeleton of the Bruhat–Tits building of
`PGL₃` over the completion of `A` at `p`. Its clique complex is the building, which is
contractible.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open scoped Pointwise

section Lattices

variable (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B] (p : A)

/-- The `A`-lattice of `B³` spanned by the columns of `g`. -/
def latOf (g : Matrix.GeneralLinearGroup (Fin 3) B) : Submodule A (Fin 3 → B) :=
  Submodule.span A (Set.range fun j : Fin 3 => fun i : Fin 3 =>
    (g : Matrix (Fin 3) (Fin 3) B) i j)

/-- Homothety by powers of `p`. -/
def Homothetic (g h : Matrix.GeneralLinearGroup (Fin 3) B) : Prop :=
  ∃ a b : ℕ, (p ^ a) • latOf A B g = (p ^ b) • latOf A B h

theorem homothetic_equivalence : Equivalence (Homothetic A B p) where
  refl _ := ⟨0, 0, rfl⟩
  symm := fun ⟨a, b, h⟩ => ⟨b, a, h.symm⟩
  trans := fun {g h k} ⟨a, b, h₁⟩ ⟨c, d, h₂⟩ => ⟨a + c, b + d, by
    calc (p ^ (a + c)) • latOf A B g = (p ^ c) • ((p ^ a) • latOf A B g) := by
          rw [smul_smul, ← pow_add, Nat.add_comm]
      _ = (p ^ c) • ((p ^ b) • latOf A B h) := by rw [h₁]
      _ = (p ^ b) • ((p ^ c) • latOf A B h) := by rw [smul_smul, smul_smul, mul_comm]
      _ = (p ^ b) • ((p ^ d) • latOf A B k) := by rw [h₂]
      _ = (p ^ (b + d)) • latOf A B k := by rw [smul_smul, ← pow_add]⟩

#audit_axioms homothetic_equivalence

/-- The homothety setoid on `GL₃(B)`. -/
def homotheticSetoid : Setoid (Matrix.GeneralLinearGroup (Fin 3) B) :=
  ⟨Homothetic A B p, homothetic_equivalence A B p⟩

/-- The vertices: homothety classes of lattices. -/
def Vertex : Type _ :=
  Quotient (homotheticSetoid A B p)

/-- The vertex of `g`. -/
def vertexOf (g : Matrix.GeneralLinearGroup (Fin 3) B) : Vertex A B p :=
  Quotient.mk (homotheticSetoid A B p) g

/-- One-sided incidence: some representatives satisfy `p • L < L' < L`. -/
def Incident (x y : Vertex A B p) : Prop :=
  ∃ g h : Matrix.GeneralLinearGroup (Fin 3) B, vertexOf A B p g = x ∧ vertexOf A B p h = y ∧
    p • latOf A B g < latOf A B h ∧ latOf A B h < latOf A B g

/-- **The 1-skeleton of the building.** -/
def buildingGraph : SimpleGraph (Vertex A B p) :=
  SimpleGraph.fromRel (Incident A B p)

/-- The standard vertex, the class of `A³`. -/
def baseVertex : Vertex A B p :=
  vertexOf A B p 1

end Lattices

section SimpleConnectivity

variable {V : Type*} (G : SimpleGraph V)

/-- One elementary move on edge paths, written as vertex lists. -/
inductive TriStep : List V → List V → Prop
  /-- Cancel a backtrack `u v u ↦ u`. -/
  | backtrack (l₁ l₂ : List V) (u v : V) (h : G.Adj u v) :
      TriStep (l₁ ++ u :: v :: u :: l₂) (l₁ ++ u :: l₂)
  /-- Push an edge across a triangle `u v w ↦ u w`. -/
  | triangle (l₁ l₂ : List V) (u v w : V) (huv : G.Adj u v) (hvw : G.Adj v w)
      (huw : G.Adj u w) :
      TriStep (l₁ ++ u :: v :: w :: l₂) (l₁ ++ u :: w :: l₂)

/-- **Simple connectivity of the clique 2-complex of `G` at `v₀`.** Every closed edge path
`v₀ :: l` (consecutive vertices adjacent, last vertex `v₀`) is equivalent to the constant path
`[v₀]` under backtracks and triangles, in either direction. -/
def TriSimplyConnected (v₀ : V) : Prop :=
  ∀ l : List V, List.IsChain G.Adj (v₀ :: l) → (v₀ :: l).getLast (List.cons_ne_nil _ _) = v₀ →
    Relation.EqvGen (TriStep G) (v₀ :: l) [v₀]

end SimpleConnectivity

/-- **Piece Z.4 (lane k2-bt-sc): the Ã₂ building is connected and simply connected.** For a PID
`A` and a prime `p ∈ A`, the lattice building graph of `B = A[1/p]` is connected. Its clique
complex is simply connected at the standard vertex. -/
def BuildingSimplyConnectedStatement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] (p : A), Prime p →
    (buildingGraph A (Localization.Away p) p).Connected ∧
      TriSimplyConnected (buildingGraph A (Localization.Away p) p)
        (baseVertex A (Localization.Away p) p)

#audit_axioms BuildingSimplyConnectedStatement

end BTri
end BooneHigmanLinear
end GroupApproximation
