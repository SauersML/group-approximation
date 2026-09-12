import GroupApproximation.Sofic.HullSuitabilityGeometry
import GroupApproximation.Meta.AxiomGuard

/-!
# The sequential Gromov boundary, limit sets, and Osin's definition of acylindrical hyperbolicity

`non_mf_groups_exist.tex` uses *acylindrically hyperbolic* in its standard sense,
Osin's: a group admitting a **non-elementary** acylindrical action on a hyperbolic
space, where an action is non-elementary when its limit set on the Gromov boundary
has more than two points (Osin, *Acylindrically hyperbolic groups*, §1).  The
repository's `TorsionFree.IsAcylindricallyHyperbolic` is Hull's Cayley-graph form;
this module provides the vocabulary in which the printed notion is stated.

The boundary of a (not necessarily proper) hyperbolic space is taken sequentially,
as for Gromov products: a sequence **converges at infinity** when its mutual
Gromov products tend to infinity, and two such sequences are **equivalent at
infinity** when the Gromov products between them tend to infinity.  Over a
hyperbolic space equivalence at infinity is an equivalence relation on convergent
sequences (`EquivAtInfinity.trans`), so its classes are the boundary points, and
the limit set of a group action is the set of classes of convergent orbit
sequences.  "The limit set has more than two points" is then literally the
existence of three pairwise inequivalent convergent orbit sequences
(`LimitSetHasMoreThanTwoPoints`); no quotient type is needed to state it, and the
choice of basepoint does not matter (`convergesAtInfinity_basepoint`,
`equivAtInfinity_basepoint`).  `IsAcylindricallyHyperbolicLimitSet` is Osin's
definition in this spelling.
-/

namespace GroupApproximation
namespace GGT
namespace SequentialBoundary

open GroupApproximation.HullGeometry

universe u v

section Space

variable {X : Type v} [PseudoMetricSpace X]

/-- **A sequence converges at infinity**: its mutual Gromov products, based at
`w`, tend to infinity. -/
def ConvergesAtInfinity (x : ℕ → X) (w : X) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → M ≤ gromovProduct (x i) (x j) w

/-- **Two sequences are equivalent at infinity**: the Gromov products between
them, based at `w`, tend to infinity.  On convergent sequences over a hyperbolic
space this is the relation whose classes are the points of the Gromov
boundary. -/
def EquivAtInfinity (x y : ℕ → X) (w : X) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → M ≤ gromovProduct (x i) (y j) w

/-- A convergent sequence is equivalent to itself: the two definitions agree on
the diagonal. -/
theorem EquivAtInfinity.refl {x : ℕ → X} {w : X} (hx : ConvergesAtInfinity x w) :
    EquivAtInfinity x x w :=
  hx

/-- Equivalence at infinity is symmetric, because the Gromov product is. -/
theorem EquivAtInfinity.symm {x y : ℕ → X} {w : X} (h : EquivAtInfinity x y w) :
    EquivAtInfinity y x w := by
  intro M
  obtain ⟨N, hN⟩ := h M
  refine ⟨N, fun i j hi hj => ?_⟩
  have h1 := hN j i hj hi
  unfold gromovProduct at h1 ⊢
  rw [dist_comm (x j) (y i)] at h1
  linarith

/-- **Equivalence at infinity is transitive over a hyperbolic space**, by the
four-point condition `min((x|y)_w, (y|z)_w) - δ ≤ (x|z)_w`. -/
theorem EquivAtInfinity.trans {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    {x y z : ℕ → X} {w : X} (hxy : EquivAtInfinity x y w)
    (hyz : EquivAtInfinity y z w) : EquivAtInfinity x z w := by
  intro M
  obtain ⟨N₁, hN₁⟩ := hxy (M + δ)
  obtain ⟨N₂, hN₂⟩ := hyz (M + δ)
  refine ⟨max N₁ N₂, fun i k hi hk => ?_⟩
  let j := max N₁ N₂
  have h1 : M + δ ≤ gromovProduct (x i) (y j) w :=
    hN₁ i j (le_trans (le_max_left _ _) hi) (le_max_left _ _)
  have h2 : M + δ ≤ gromovProduct (y j) (z k) w :=
    hN₂ j k (le_max_right _ _) (le_trans (le_max_right _ _) hk)
  have h4 := hδ w (x i) (y j) (z k)
  have hmin : M + δ ≤ min (gromovProduct (x i) (y j) w)
      (gromovProduct (y j) (z k) w) := le_min h1 h2
  linarith

/-- **Changing the basepoint moves a Gromov product by at most the distance
between the basepoints.** -/
theorem abs_gromovProduct_sub_gromovProduct_le (x y w w' : X) :
    |gromovProduct x y w - gromovProduct x y w'| ≤ dist w w' := by
  unfold gromovProduct
  have h1 := dist_triangle x w w'
  have h2 := dist_triangle x w' w
  have h3 := dist_triangle y w w'
  have h4 := dist_triangle y w' w
  rw [dist_comm w' w] at h2 h4
  rw [abs_le]
  constructor <;> linarith

/-- Convergence at infinity does not depend on the basepoint. -/
theorem convergesAtInfinity_basepoint {x : ℕ → X} {w w' : X}
    (h : ConvergesAtInfinity x w) : ConvergesAtInfinity x w' := by
  intro M
  obtain ⟨N, hN⟩ := h (M + dist w w')
  refine ⟨N, fun i j hi hj => ?_⟩
  have h1 := hN i j hi hj
  have h2 := abs_le.mp (abs_gromovProduct_sub_gromovProduct_le (x i) (x j) w w')
  linarith [h2.1]

/-- Equivalence at infinity does not depend on the basepoint. -/
theorem equivAtInfinity_basepoint {x y : ℕ → X} {w w' : X}
    (h : EquivAtInfinity x y w) : EquivAtInfinity x y w' := by
  intro M
  obtain ⟨N, hN⟩ := h (M + dist w w')
  refine ⟨N, fun i j hi hj => ?_⟩
  have h1 := hN i j hi hj
  have h2 := abs_le.mp (abs_gromovProduct_sub_gromovProduct_le (x i) (y j) w w')
  linarith [h2.1]

/-- **Bounded Gromov products separate boundary points**: if the products between
two sequences stay bounded, the sequences are not equivalent at infinity. -/
theorem not_equivAtInfinity_of_bounded {x y : ℕ → X} {w : X} {C : ℝ}
    (hC : ∀ i j : ℕ, gromovProduct (x i) (y j) w ≤ C) :
    ¬ EquivAtInfinity x y w := by
  intro h
  obtain ⟨N, hN⟩ := h (C + 1)
  have h1 := hN N N le_rfl le_rfl
  have h2 := hC N N
  linarith

end Space

section Action

variable (G : Type u) [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **The limit set of the action has more than two points** (Osin's
non-elementarity): there are three orbit sequences, each converging at infinity,
that are pairwise inequivalent at infinity. -/
def LimitSetHasMoreThanTwoPoints (w : X) : Prop :=
  ∃ a b c : ℕ → G,
    ConvergesAtInfinity (fun i => a i • w) w ∧
      ConvergesAtInfinity (fun i => b i • w) w ∧
        ConvergesAtInfinity (fun i => c i • w) w ∧
          ¬ EquivAtInfinity (fun i => a i • w) (fun i => b i • w) w ∧
            ¬ EquivAtInfinity (fun i => b i • w) (fun i => c i • w) w ∧
              ¬ EquivAtInfinity (fun i => a i • w) (fun i => c i • w) w

/-- **A non-elementary action**: the limit set has more than two points. -/
def IsNonElementaryAction : Prop :=
  ∃ w : X, LimitSetHasMoreThanTwoPoints G w

end Action

/-- **Osin's definition of an acylindrically hyperbolic group, limit-set
spelling**: `G` admits an acylindrical isometric action on a geodesic hyperbolic
space whose limit set has more than two points.

Osin, *Acylindrically hyperbolic groups*, §1, with hyperbolic spaces geodesic and
non-elementarity the limit-set condition.  `GGT.AcylindricallyHyperbolicOsin`
states the same definition with non-elementarity spelled as two independent
loxodromic elements (Osin's Theorem 1.1 makes the two spellings agree for
acylindrical actions).  Stated for groups in `Type`. -/
def IsAcylindricallyHyperbolicLimitSet (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (_ : PseudoMetricSpace X) (_ : MulAction G X),
    IsIsometricAction G X ∧ IsGeodesicSpace X ∧ (∃ δ : ℝ, IsHyperbolicSpace δ X) ∧
      IsAcylindrical G X ∧ IsNonElementaryAction G (X := X)

end SequentialBoundary
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.SequentialBoundary.EquivAtInfinity.symm
#audit_axioms GroupApproximation.GGT.SequentialBoundary.EquivAtInfinity.trans
#audit_axioms GroupApproximation.GGT.SequentialBoundary.abs_gromovProduct_sub_gromovProduct_le
#audit_axioms GroupApproximation.GGT.SequentialBoundary.convergesAtInfinity_basepoint
#audit_axioms GroupApproximation.GGT.SequentialBoundary.equivAtInfinity_basepoint
#audit_axioms GroupApproximation.GGT.SequentialBoundary.not_equivAtInfinity_of_bounded
