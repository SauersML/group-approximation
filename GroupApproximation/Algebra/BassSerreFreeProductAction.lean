import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The Bass--Serre coset action of a binary free product

This file isolates the part of the Bass--Serre tree construction that is
already completely algebraic.  For `F = G ∗ Multiplicative ℤ`, its vertices
are the left cosets of the two free factors and its edges are the translates
of the pair of base cosets.  Left multiplication gives the canonical action.

The key output is `baseEdge_pointwiseStabilizer_eq_bot`: the pointwise
stabilizer of the base edge is trivial.  This is the finite-stabilizer input in
the WPD/acylindricity argument, proved directly from the two free-product
retractions.  No tree, hyperbolicity, or acylindricity assertion is stored as
an input here.  The remaining geometric step is to identify the graph below
with a tree using the reduced-word normal form.
-/

namespace GroupApproximation
namespace BassSerreFreeProduct

open Monoid

universe u

variable (G : Type u) [Group G]

/-- The free product used in the pivot. -/
abbrev Ambient := Monoid.Coprod G (Multiplicative ℤ)

/-- The canonical copy of the left factor. -/
def leftFactor : Subgroup (Ambient G) :=
  MonoidHom.range (Monoid.Coprod.inl : G →* Ambient G)

/-- The canonical copy of the infinite cyclic right factor. -/
def rightFactor : Subgroup (Ambient G) :=
  MonoidHom.range
    (Monoid.Coprod.inr : Multiplicative ℤ →* Ambient G)

/-- The two free factors meet only in the identity. -/
theorem leftFactor_inf_rightFactor :
    leftFactor G ⊓ rightFactor G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx.1 with ⟨a, ha⟩
  rcases hx.2 with ⟨b, hb⟩
  have hab :
      (Monoid.Coprod.inl a : Ambient G) = Monoid.Coprod.inr b :=
    ha.trans hb.symm
  have haone : a = 1 := by
    have := congrArg (Monoid.Coprod.fst : Ambient G →* G) hab
    simpa using this
  rw [← ha, haone, map_one]

/-- Vertices of the Bass--Serre coset graph: one color for each factor. -/
abbrev Vertex :=
  (Ambient G ⧸ leftFactor G) ⊕ (Ambient G ⧸ rightFactor G)

/-- Left multiplication on the two colors of cosets. -/
instance vertexMulAction : MulAction (Ambient G) (Vertex G) where
  smul g
    | Sum.inl x => Sum.inl (g • x)
    | Sum.inr x => Sum.inr (g • x)
  one_smul := by
    intro x
    cases x <;> simp
  mul_smul := by
    intro g h x
    cases x <;> simp [mul_smul]

/-- The base vertex of left-factor color. -/
def baseLeft : Vertex G :=
  Sum.inl (1 : Ambient G ⧸ leftFactor G)

/-- The base vertex of right-factor color. -/
def baseRight : Vertex G :=
  Sum.inr (1 : Ambient G ⧸ rightFactor G)

/-- An oriented edge is a translate of the two base cosets. -/
def IsOrientedEdge (v w : Vertex G) : Prop :=
  ∃ g : Ambient G, v = g • baseLeft G ∧ w = g • baseRight G

/-- The (undirected) Bass--Serre coset graph. -/
def graph : SimpleGraph (Vertex G) where
  Adj v w := IsOrientedEdge G v w ∨ IsOrientedEdge G w v
  symm := by
    intro v w h
    exact h.elim Or.inr Or.inl
  loopless := by
    intro v h
    rcases h with ⟨g, hv, hw⟩ | ⟨g, hv, hw⟩
    · have : g • baseLeft G = g • baseRight G := hv.symm.trans hw
      simpa [baseLeft, baseRight] using this
    · have : g • baseRight G = g • baseLeft G := hv.symm.trans hw
      simpa [baseLeft, baseRight] using this

/-- The action carries oriented edges to oriented edges. -/
theorem isOrientedEdge_smul (a : Ambient G) {v w : Vertex G}
    (h : IsOrientedEdge G v w) :
    IsOrientedEdge G (a • v) (a • w) := by
  obtain ⟨g, rfl, rfl⟩ := h
  exact ⟨a * g, by simp [mul_smul], by simp [mul_smul]⟩

/-- Left multiplication preserves adjacency in both directions. -/
theorem adj_smul_iff (a : Ambient G) (v w : Vertex G) :
    (graph G).Adj (a • v) (a • w) ↔ (graph G).Adj v w := by
  change
    (IsOrientedEdge G (a • v) (a • w) ∨
      IsOrientedEdge G (a • w) (a • v)) ↔
    (IsOrientedEdge G v w ∨ IsOrientedEdge G w v)
  constructor
  · intro h
    rcases h with hvw | hwv
    · left
      simpa only [inv_smul_smul] using isOrientedEdge_smul G a⁻¹ hvw
    · right
      simpa only [inv_smul_smul] using isOrientedEdge_smul G a⁻¹ hwv
  · intro h
    exact h.elim (fun hvw ↦ Or.inl (isOrientedEdge_smul G a hvw))
      (fun hwv ↦ Or.inr (isOrientedEdge_smul G a hwv))

/-- Left multiplication as a graph homomorphism. -/
def actionHom (a : Ambient G) : graph G →g graph G where
  toFun v := a • v
  map_rel' := fun {_ _} h ↦ (adj_smul_iff G a _ _).mpr h

/-- Reachability is preserved by left multiplication. -/
theorem Reachable.smul (a : Ambient G) {v w : Vertex G}
    (h : (graph G).Reachable v w) :
    (graph G).Reachable (a • v) (a • w) :=
  h.map (actionHom G a)

/-- The two base vertices form an edge. -/
theorem base_adj : (graph G).Adj (baseLeft G) (baseRight G) :=
  Or.inl ⟨1, by simp [baseLeft], by simp [baseRight]⟩

/-- Fixing the left base coset is exactly membership in the left factor. -/
theorem smul_baseLeft_eq_iff (g : Ambient G) :
    g • baseLeft G = baseLeft G ↔ g ∈ leftFactor G := by
  change
    (g • (1 : Ambient G ⧸ leftFactor G)) = 1 ↔
      g ∈ leftFactor G
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simp

/-- Fixing the right base coset is exactly membership in the right factor. -/
theorem smul_baseRight_eq_iff (g : Ambient G) :
    g • baseRight G = baseRight G ↔ g ∈ rightFactor G := by
  change
    (g • (1 : Ambient G ⧸ rightFactor G)) = 1 ↔
      g ∈ rightFactor G
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simp

/-- Every translate of either base vertex is reachable from the left base
vertex.  This uses only the coproduct induction principle: a left-factor
letter fixes `baseLeft`, while a right-factor letter fixes `baseRight` and
crosses the base edge. -/
theorem reachable_translates (g : Ambient G) :
    (graph G).Reachable (baseLeft G) (g • baseLeft G) ∧
      (graph G).Reachable (baseLeft G) (g • baseRight G) := by
  induction g using Monoid.Coprod.induction_on' with
  | one =>
      exact ⟨by simp, (base_adj G).reachable⟩
  | inl_mul a x ih =>
      have hfix :
          (Monoid.Coprod.inl a : Ambient G) • baseLeft G = baseLeft G :=
        (smul_baseLeft_eq_iff G _).mpr ⟨a, rfl⟩
      constructor
      · simpa only [mul_smul, hfix] using
          ih.1.smul G (Monoid.Coprod.inl a : Ambient G)
      · simpa only [mul_smul, hfix] using
          ih.2.smul G (Monoid.Coprod.inl a : Ambient G)
  | inr_mul b x ih =>
      have hfix :
          (Monoid.Coprod.inr b : Ambient G) • baseRight G = baseRight G :=
        (smul_baseRight_eq_iff G _).mpr ⟨b, rfl⟩
      have hcross : (graph G).Reachable (baseLeft G)
          ((Monoid.Coprod.inr b : Ambient G) • baseLeft G) :=
        (base_adj G).reachable.trans <| by
          have := (base_adj G).reachable.smul G
            (Monoid.Coprod.inr b : Ambient G)
          simpa only [hfix] using this.symm
      constructor
      · exact hcross.trans <| by
          simpa only [mul_smul] using
            ih.1.smul G (Monoid.Coprod.inr b : Ambient G)
      · exact hcross.trans <| by
          simpa only [mul_smul] using
            ih.2.smul G (Monoid.Coprod.inr b : Ambient G)

/-- Every vertex is reachable from the left base vertex. -/
theorem reachable_from_baseLeft (v : Vertex G) :
    (graph G).Reachable (baseLeft G) v := by
  rcases v with v | v
  · refine QuotientGroup.induction_on v ?_
    intro g
    exact (reachable_translates G g).1
  · refine QuotientGroup.induction_on v ?_
    intro g
    exact (reachable_translates G g).2

/-- The Bass--Serre coset graph is connected. -/
theorem graph_connected : (graph G).Connected := by
  refine ⟨?_, ⟨baseLeft G⟩⟩
  intro v w
  exact (reachable_from_baseLeft G v).symm.trans (reachable_from_baseLeft G w)

/-- The ordered endpoints of the base edge. -/
def baseEdge : Vertex G × Vertex G := (baseLeft G, baseRight G)

/-- An element fixing both endpoints of the base edge is the identity. -/
theorem smul_baseEdge_eq_iff (g : Ambient G) :
    g • baseEdge G = baseEdge G ↔ g = 1 := by
  constructor
  · intro h
    have hleft : g • baseLeft G = baseLeft G := congrArg Prod.fst h
    have hright : g • baseRight G = baseRight G := congrArg Prod.snd h
    have hg : g ∈ leftFactor G ⊓ rightFactor G :=
      ⟨(smul_baseLeft_eq_iff G g).mp hleft,
        (smul_baseRight_eq_iff G g).mp hright⟩
    rw [leftFactor_inf_rightFactor G] at hg
    simpa using hg
  · rintro rfl
    exact one_smul _ _

/-- **The base edge has trivial pointwise stabilizer.**  In particular it is
finite, which is the algebraic core of the WPD segment argument for the
Bass--Serre action. -/
theorem baseEdge_pointwiseStabilizer_eq_bot :
    MulAction.stabilizer (Ambient G) (baseEdge G) = ⊥ := by
  ext g
  rw [MulAction.mem_stabilizer_iff, smul_baseEdge_eq_iff G]
  exact (Subgroup.mem_bot).symm

/-- The base-edge pointwise stabilizer is finite (indeed, trivial). -/
theorem finite_baseEdge_pointwiseStabilizer :
    Finite (MulAction.stabilizer (Ambient G) (baseEdge G)) := by
  rw [baseEdge_pointwiseStabilizer_eq_bot G]
  infer_instance

/-- Every translate of the base edge has trivial pointwise stabilizer. -/
theorem smul_translatedBaseEdge_eq_iff (g x : Ambient G) :
    x • (g • baseEdge G) = g • baseEdge G ↔ x = 1 := by
  constructor
  · intro h
    have hc : (g⁻¹ * x * g) • baseEdge G = baseEdge G := by
      calc
        (g⁻¹ * x * g) • baseEdge G =
            g⁻¹ • (x • (g • baseEdge G)) := by simp [mul_smul]
        _ = g⁻¹ • (g • baseEdge G) := by rw [h]
        _ = baseEdge G := inv_smul_smul g _
    have hconj : g⁻¹ * x * g = 1 :=
      (smul_baseEdge_eq_iff G (g⁻¹ * x * g)).mp hc
    calc
      x = g * (g⁻¹ * x * g) * g⁻¹ := by simp [mul_assoc]
      _ = 1 := by rw [hconj]; simp
  · rintro rfl
    exact one_smul _ _

/-- Every translated oriented edge has trivial pointwise stabilizer. -/
theorem translatedBaseEdge_pointwiseStabilizer_eq_bot (g : Ambient G) :
    MulAction.stabilizer (Ambient G) (g • baseEdge G) = ⊥ := by
  ext x
  rw [MulAction.mem_stabilizer_iff, smul_translatedBaseEdge_eq_iff G]
  exact (Subgroup.mem_bot).symm

/-- **Every edge of the Bass--Serre coset graph has trivial pointwise
stabilizer.**  This is the zero-error edge-stabilizer input to the usual
acylindricity argument; by itself it does not assert the bounded-displacement
quantifiers in the definition of an acylindrical action.  It also does not
depend on the still-separate proof that the graph is a tree. -/
theorem adjacentPair_pointwiseStabilizer_eq_bot {v w : Vertex G}
    (hvw : (graph G).Adj v w) :
    MulAction.stabilizer (Ambient G) (v, w) = ⊥ := by
  change IsOrientedEdge G v w ∨ IsOrientedEdge G w v at hvw
  rcases hvw with ⟨g, rfl, rfl⟩ | ⟨g, rfl, rfl⟩
  · change MulAction.stabilizer (Ambient G) (g • baseEdge G) = ⊥
    exact translatedBaseEdge_pointwiseStabilizer_eq_bot G g
  · ext x
    rw [MulAction.mem_stabilizer_iff]
    change
      (x • (g • baseRight G), x • (g • baseLeft G)) =
          (g • baseRight G, g • baseLeft G) ↔ x ∈ (⊥ : Subgroup (Ambient G))
    rw [Prod.mk.injEq, and_comm]
    change x • (g • baseEdge G) = g • baseEdge G ↔ _
    rw [smul_translatedBaseEdge_eq_iff G]
    exact (Subgroup.mem_bot).symm

/-- In particular, the pointwise stabilizer of every graph edge is finite. -/
theorem finite_adjacentPair_pointwiseStabilizer {v w : Vertex G}
    (hvw : (graph G).Adj v w) :
    Finite (MulAction.stabilizer (Ambient G) (v, w)) := by
  rw [adjacentPair_pointwiseStabilizer_eq_bot G hvw]
  infer_instance

end BassSerreFreeProduct
end GroupApproximation
