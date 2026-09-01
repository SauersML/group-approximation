import Mathlib.Combinatorics.SimpleGraph.Basic
import GroupApproximation.GGT.DGOTheorem442ProjectionMonotone

/-!
# The first projection-complex construction layer

DGO Definition 4.1 next replaces the original projection distances by a
perturbed family `d_Y` satisfying

`|dᵖ_Y(A,B) - d_Y(A,B)| ≤ 2ξ`

and joins `A` to `B` when every third vertex has `d_Y(A,B) ≤ K`.  This
file formalizes exactly that construction.  It does not assume the later BBF
connectedness or quasi-tree theorem.

There is one useful finiteness point already available from (A4).  If
`K ≥ 3ξ`, every blocker for the perturbed graph is large for the original
projection system, hence the blocker set is finite.  Thus the universal edge
condition is controlled by an explicit finite set.  For equivariant
perturbations, the given group action preserves edges, which is the first
construction assertion made after DGO's definition.
-/

namespace GroupApproximation
namespace GGT

universe u v

/-- A nonnegative symmetric perturbation of a projection system within the
exact non-strict `2ξ` bound obtained from the BBF infimum construction. -/
structure ProjectionPerturbation {V : Type u} (P : ProjectionSystem V) where
  projDist : V → V → V → ℝ
  nonneg : ∀ Y A B, 0 ≤ projDist Y A B
  comm : ∀ Y A B, projDist Y A B = projDist Y B A
  close : ∀ Y A B, Y ≠ A → Y ≠ B →
    |P.projDist Y A B - projDist Y A B| ≤ 2 * P.ξ
  endpoints_lt : ∀ Y A B, Y ≠ A → Y ≠ B → A ≠ B →
    2 * P.ξ < projDist Y A B →
      projDist A Y B < P.ξ ∧ projDist B A Y < P.ξ

namespace ProjectionPerturbation

variable {V : Type u} {P : ProjectionSystem V}

/-- The actual BBF infimum perturbation.  Proposition 2.2 gives precisely the
non-strict `2ξ` estimate after taking the infimum. -/
noncomputable def bbf (P : ProjectionSystem V) : ProjectionPerturbation P where
  projDist := P.bbfProjDist
  nonneg := P.bbfProjDist_nonneg
  comm := P.bbfProjDist_comm
  close := by
    intro Y A B hYA hYB
    rw [abs_le]
    constructor
    · have hle := P.bbfProjDist_le hYA hYB
      linarith [P.ξ_pos]
    · have hle := P.projDist_sub_bbfProjDist_le_two_mul hYA hYB
      linarith
  endpoints_lt := P.bbfProjDist_endpoints_lt

/-- Third vertices obstructing the edge from `A` to `B` at threshold `K`. -/
def blockers (Q : ProjectionPerturbation P) (K : ℝ) (A B : V) : Set V :=
  {Y | Y ≠ A ∧ Y ≠ B ∧ K < Q.projDist Y A B}

/-- The graph underlying the projection-complex construction at threshold
`K`. -/
def graph (Q : ProjectionPerturbation P) (K : ℝ) : SimpleGraph V where
  Adj A B := A ≠ B ∧ ∀ Y, Y ≠ A → Y ≠ B → Q.projDist Y A B ≤ K
  symm := ⟨by
    intro A B h
    refine ⟨h.1.symm, ?_⟩
    intro Y hYB hYA
    rw [Q.comm]
    exact h.2 Y hYA hYB⟩
  loopless := ⟨by
    intro A h
    exact h.1 rfl⟩

@[simp] theorem graph_adj_iff (Q : ProjectionPerturbation P) (K : ℝ)
    (A B : V) :
    (Q.graph K).Adj A B ↔
      A ≠ B ∧ ∀ Y, Y ≠ A → Y ≠ B → Q.projDist Y A B ≤ K :=
  Iff.rfl

/-- Adjacency is exactly the absence of blockers, together with distinctness
of the endpoints. -/
theorem graph_adj_iff_blockers_eq_empty
    (Q : ProjectionPerturbation P) (K : ℝ) (A B : V) :
    (Q.graph K).Adj A B ↔ A ≠ B ∧ Q.blockers K A B = ∅ := by
  rw [graph_adj_iff]
  constructor
  · rintro ⟨hAB, hbound⟩
    refine ⟨hAB, ?_⟩
    ext Y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hY
    exact (not_lt_of_ge (hbound Y hY.1 hY.2.1)) hY.2.2
  · rintro ⟨hAB, hempty⟩
    refine ⟨hAB, ?_⟩
    intro Y hYA hYB
    by_contra hnot
    have hblock : Y ∈ Q.blockers K A B := ⟨hYA, hYB, lt_of_not_ge hnot⟩
    rw [hempty] at hblock
    exact hblock

/-- For `K ≥ 3ξ`, the set of possible edge blockers is finite.  Indeed the
`2ξ` perturbation estimate turns `d_Y(A,B) > K` into
`dᵖ_Y(A,B) ≥ ξ`, and (A4) applies. -/
theorem blockers_finite (Q : ProjectionPerturbation P)
    {K : ℝ} (hK : 3 * P.ξ ≤ K) {A B : V} (hAB : A ≠ B) :
    (Q.blockers K A B).Finite := by
  refine (P.largeSet_finite hAB).subset ?_
  intro Y hY
  have hclose := Q.close Y A B hY.1 hY.2.1
  have hlower := (abs_le.mp hclose).1
  change P.ξ ≤ P.projDist Y A B
  linarith [hY.2.2]

end ProjectionPerturbation

/-- An allowed perturbation which is itself preserved by the group action. -/
structure EquivariantProjectionPerturbation
    (G : Type u) (V : Type v) [Group G] [MulAction G V]
    (P : EquivariantProjectionSystem G V)
    extends ProjectionPerturbation P.toProjectionSystem where
  smul_projDist : ∀ (g : G) (Y A B : V),
    projDist (g • Y) (g • A) (g • B) = projDist Y A B

namespace EquivariantProjectionPerturbation

variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
  {P : EquivariantProjectionSystem G V}

/-- The source-faithful BBF infimum perturbation, with equivariance inherited
from simultaneous translation of its admissible candidate pairs. -/
noncomputable def bbf (P : EquivariantProjectionSystem G V) :
    EquivariantProjectionPerturbation G V P where
  toProjectionPerturbation := ProjectionPerturbation.bbf P.toProjectionSystem
  smul_projDist := P.bbfProjDist_smul

/-- Every group element sends an edge of the projection graph to an edge. -/
theorem graph_adj_smul (Q : EquivariantProjectionPerturbation G V P)
    (K : ℝ) (g : G) {A B : V}
    (hAB : (Q.toProjectionPerturbation.graph K).Adj A B) :
    (Q.toProjectionPerturbation.graph K).Adj (g • A) (g • B) := by
  rw [ProjectionPerturbation.graph_adj_iff] at hAB ⊢
  refine ⟨?_, ?_⟩
  · intro heq
    apply hAB.1
    have := congrArg (fun Z : V => g⁻¹ • Z) heq
    simpa using this
  · intro Z hZA hZB
    obtain ⟨Y, rfl⟩ : ∃ Y : V, g • Y = Z := ⟨g⁻¹ • Z, by simp⟩
    have hYA : Y ≠ A := by
      intro h
      subst Y
      exact hZA rfl
    have hYB : Y ≠ B := by
      intro h
      subst Y
      exact hZB rfl
    rw [Q.smul_projDist]
    exact hAB.2 Y hYA hYB

/-- The action preserves adjacency in both directions, so it extends to the
projection graph exactly as stated after DGO Definition 4.1. -/
theorem graph_adj_smul_iff (Q : EquivariantProjectionPerturbation G V P)
    (K : ℝ) (g : G) (A B : V) :
    (Q.toProjectionPerturbation.graph K).Adj (g • A) (g • B) ↔
      (Q.toProjectionPerturbation.graph K).Adj A B := by
  constructor
  · intro h
    have hback := Q.graph_adj_smul K g⁻¹ h
    simpa using hback
  · exact Q.graph_adj_smul K g

end EquivariantProjectionPerturbation

namespace Elementary

open GroupApproximation.HullGeometry

universe w

variable {G : Type u} [Group G] {S : Type w} [PseudoMetricSpace S]
  [MulAction G S]

/-- The first projection graph attached to the coset-orbit projection system,
using the source-faithful BBF infimum perturbation. -/
noncomputable def approxCosetProjectionComplex
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) (K : ℝ) : SimpleGraph (G ⧸ H) :=
  let P := approxCosetEquivariantProjectionSystem
    hδ hδ0 hδpos hgeo hiso H s hqc hsep
  (EquivariantProjectionPerturbation.bbf P).toProjectionPerturbation.graph K

/-- Simultaneous left translation preserves the adjacency relation in the
coset-orbit projection graph. -/
theorem approxCosetProjectionComplex_adj_smul_iff
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) (K : ℝ)
    (g : G) (A B : G ⧸ H) :
    (approxCosetProjectionComplex hδ hδ0 hδpos hgeo hiso H s hqc hsep K).Adj
        (g • A) (g • B) ↔
      (approxCosetProjectionComplex hδ hδ0 hδpos hgeo hiso H s hqc hsep K).Adj
        A B := by
  exact EquivariantProjectionPerturbation.graph_adj_smul_iff
    (EquivariantProjectionPerturbation.bbf
      (approxCosetEquivariantProjectionSystem
        hδ hδ0 hδpos hgeo hiso H s hqc hsep)) K g A B

/-- At every source-faithful threshold `K ≥ 3ξ`, each pair of distinct
coset vertices has only finitely many possible blockers for adjacency. -/
theorem approxCosetProjectionComplex_blockers_finite
    {δ : ℝ} (hδ : IsHyperbolicSpace δ S) (hδ0 : 0 ≤ δ) (hδpos : 0 < δ)
    (hgeo : IsGeodesicSpace S) (hiso : IsIsometricAction G S)
    (H : Subgroup G) (s : S) (hqc : IsQuasiconvexOrbitAt H s)
    (hsep : GeometricallySeparatedAt H s) :
    let P := approxCosetEquivariantProjectionSystem
      hδ hδ0 hδpos hgeo hiso H s hqc hsep
    ∀ {K : ℝ}, 3 * P.ξ ≤ K → ∀ {A B : G ⧸ H}, A ≠ B →
      ((EquivariantProjectionPerturbation.bbf P).toProjectionPerturbation.blockers
        K A B).Finite := by
  dsimp only
  intro K hK A B hAB
  exact ProjectionPerturbation.blockers_finite _ hK hAB

end Elementary
end GGT
end GroupApproximation
