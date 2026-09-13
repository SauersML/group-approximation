import GroupApproximation.GGT.SystolicTriangleCondition
import GroupApproximation.GGT.SystolicDiscFilling
import GroupApproximation.GGT.SystolicDiscMovesChord
import GroupApproximation.Meta.AxiomGuard

/-!
# Invariant cliques in systolic triangle complexes

A finite group of graph automorphisms of the connected, locally finite one-skeleton of a simply
connected triangle complex with 6-large links maps some nonempty clique into itself.

The one-skeleton satisfies the projection clique and triangle conditions and has no induced
four- or five-cycles.  Fix a vertex `o`, and let `R` bound the distances from the orbit of `o` to
`o`.  The intersection `H` of the balls of radius `R` about the orbit is finite, contains `o`, and
is invariant under the group, since graph automorphisms preserve distance.  So `H` is dismantlable
(`dismantlable_of_forall_dist_le`) and contains an invariant clique
(`Dismantlable.exists_invariantClique`).

* `dist_iso`: graph automorphisms of a connected graph preserve distance.
* `exists_invariantClique_of_graphConditions`: invariant cliques from the graph conditions.
* `exists_invariantClique_of_linksSixLarge`: invariant cliques in simply connected triangle
  complexes with 6-large links, over the zip move and the mirror fold of triangulated discs.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

universe u

section Graph

variable {V : Type*} {G : SimpleGraph V}

theorem dist_iso_le (hconn : G.Connected) (f : G ≃g G) (a b : V) :
    G.dist (f a) (f b) ≤ G.dist a b := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a b
  calc G.dist (f a) (f b) ≤ (p.map f.toHom).length := SimpleGraph.dist_le _
    _ = G.dist a b := by rw [SimpleGraph.Walk.length_map, hp]

/-- Graph automorphisms of a connected graph preserve distance. -/
theorem dist_iso (hconn : G.Connected) (f : G ≃g G) (a b : V) :
    G.dist (f a) (f b) = G.dist a b := by
  have h1 := dist_iso_le hconn f a b
  have h2 := dist_iso_le hconn f⁻¹ (f a) (f b)
  rw [RelIso.inv_apply_self, RelIso.inv_apply_self] at h2
  omega

/-- **Invariant cliques from the graph conditions.**  A finite group of automorphisms of a
connected, locally finite graph with projection cliques, the triangle condition and no induced
four- or five-cycles maps some nonempty clique into itself. -/
theorem exists_invariantClique_of_graphConditions (hconn : G.Connected)
    (hF1 : ProjectionClique G) (hF2 : TriangleCondition G) (hC4 : NoInducedFourCycle G)
    (hC5 : NoInducedFiveCycle G) (hfin : ∀ v, (G.neighborSet v).Finite) {Γ : Type*} [Group Γ]
    [Finite Γ] (ρ : Γ →* (G ≃g G)) :
    ∃ σ : Finset V, σ.Nonempty ∧ G.IsClique (σ : Set V) ∧ ∀ γ : Γ, ∀ x ∈ σ, ρ γ x ∈ σ := by
  classical
  obtain ⟨o⟩ := hconn.nonempty
  -- The orbit of `o`.
  have horb : (Set.range fun γ : Γ => ρ γ o).Finite := Set.finite_range _
  obtain ⟨S, hS⟩ : ∃ S : Finset V, ∀ s, s ∈ S ↔ ∃ γ : Γ, ρ γ o = s :=
    ⟨horb.toFinset, fun s => horb.mem_toFinset.trans Set.mem_range⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ s ∈ S, G.dist s o ≤ R :=
    ⟨S.sup fun s => G.dist s o, fun s hs => Finset.le_sup (f := fun s => G.dist s o) hs⟩
  -- The intersection of the balls of radius `R` about the orbit.
  have h1 : ρ 1 o ∈ S := (hS _).mpr ⟨1, rfl⟩
  have hball : {x | ∀ s ∈ S, G.dist s x ≤ R}.Finite := by
    refine (finite_setOf_dist_le hfin (ρ 1 o) R).subset ?_
    intro x hx
    exact ⟨hconn.preconnected _ _, hx _ h1⟩
  obtain ⟨H, hH⟩ : ∃ H : Finset V, ∀ x, x ∈ H ↔ ∀ s ∈ S, G.dist s x ≤ R :=
    ⟨hball.toFinset, fun x => hball.mem_toFinset⟩
  have ho : o ∈ H := (hH o).mpr hR
  have hdis := dismantlable_of_forall_dist_le hconn hF1 hF2 hC4 hC5 hH ⟨o, ho⟩
  have hinv : ∀ γ : Γ, ∀ x ∈ H, ρ γ x ∈ H := by
    intro γ x hx
    refine (hH _).mpr fun s hs => ?_
    obtain ⟨δ, rfl⟩ := (hS s).mp hs
    have e : ρ δ o = ρ γ (ρ (γ⁻¹ * δ) o) := by
      rw [map_mul, map_inv]
      exact (RelIso.apply_inv_self (ρ γ) (ρ δ o)).symm
    rw [e, dist_iso hconn]
    exact (hH x).mp hx _ ((hS _).mpr ⟨γ⁻¹ * δ, rfl⟩)
  obtain ⟨σ, hne, -, hcl, hσ⟩ := hdis.exists_invariantClique ρ hinv
  exact ⟨σ, hne, hcl, hσ⟩

end Graph

variable {V : Type u} {X : TriangleComplex V}

/-- **Invariant cliques in systolic triangle complexes.**  A finite group of graph automorphisms
of the connected, locally finite one-skeleton of a simply connected triangle complex with 6-large
links maps some nonempty clique into itself.  Simple connectivity enters through the zip move
`hzip` and the mirror fold `hfold` of triangulated discs. -/
theorem exists_invariantClique_of_linksSixLarge (hzip : ZipSpurStatement X)
    (hfold : MirrorFoldStatement X) (hsc : SimplyConnected X) (hconn : X.G.Connected)
    (h6 : LinksSixLarge X) (hfin : ∀ v, (X.G.neighborSet v).Finite) {Γ : Type*} [Group Γ]
    [Finite Γ] (ρ : Γ →* (X.G ≃g X.G)) :
    ∃ σ : Finset V, σ.Nonempty ∧ X.G.IsClique (σ : Set V) ∧ ∀ γ : Γ, ∀ x ∈ σ, ρ γ x ∈ σ := by
  have hfill := fillingStatement_of_simplyConnected hsc attachTriangleStatement
    insertChordStatement attachPendantStatement hzip
  exact exists_invariantClique_of_graphConditions hconn
    (projectionClique_of_linksSixLarge hfill hfold h6 hconn)
    (triangleCondition_of_linksSixLarge hfill hfold h6 hconn)
    (noInducedFourCycle_of_linksSixLarge hfill hfold h6)
    (noInducedFiveCycle_of_linksSixLarge hfill hfold h6) hfin ρ

end Systolic
end GroupApproximation

open GroupApproximation.Systolic

#audit_axioms dist_iso_le
#audit_axioms dist_iso
#audit_axioms exists_invariantClique_of_graphConditions
#audit_axioms exists_invariantClique_of_linksSixLarge
