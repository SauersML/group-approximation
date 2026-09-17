import GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoid.KasparovOp
import GroupApproximation.Meta.AxiomGuard

/-!
# Norm-continuous paths of Kasparov operators

Fix a frame `(E, γ, ρ)`.  `OpPath E γ ρ F G` says that there is a norm-continuous path
`P : ℝ → 𝓛(E)` of Kasparov operators on the frame with `P 0 = F` and `P 1 = G` pointwise.
A path is defined on all of `ℝ`, so no interval subtype appears.  Norm continuity is stated with
the corpus bound `IsBoundedBy`: `‖(P s - P t)x‖ ≤ ε‖x‖` whenever `|s - t| < δ`.

## The proof route

* `OpPath.refl`: the constant path.  `P t - P t` is bounded by any `ε ≥ 0`
  (`isBoundedBy_sub_self`).
* `OpPath.symm`: `s ↦ P (1 - s)`.
* `OpPath.trans`: `concatPath P Q s = P (c(2s)) + Q (c(2s - 1)) - P 1`, where
  `c = clamp01 = max 0 (min · 1)`.  For `s ≤ 1/2`, `c(2s - 1) = 0` and `Q 0 = G = P 1`, so the
  sum is `P (c(2s))`.  For `s ≥ 1/2`, `c(2s) = 1`, so the sum is `Q (c(2s - 1))`.  So every
  `concatPath P Q s` is a Kasparov operator (`IsKasparovOp.congr`).  Continuity uses one formula
  for all `s`: `c` is `1`-Lipschitz (`abs_clamp01_sub_le`), and the difference of two values is
  a sum of a `P`-difference and a `Q`-difference.
* `OpPath.prodMap_right`: `s ↦ P s ⊞ K` is a path from `F ⊞ K` to `G ⊞ K`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KKMonoidLane

open HilbertModule

universe u v w w'

/-- The clamp of `s` to `[0, 1]`. -/
def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.clamp01

theorem clamp01_of_nonpos {s : ℝ} (hs : s ≤ 0) : clamp01 s = 0 := by
  show max 0 (min s 1) = 0
  exact max_eq_left (le_trans (min_le_left s 1) hs)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.clamp01_of_nonpos

theorem clamp01_of_one_le {s : ℝ} (hs : 1 ≤ s) : clamp01 s = 1 := by
  show max 0 (min s 1) = 1
  rw [min_eq_right hs]
  exact max_eq_right zero_le_one

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.clamp01_of_one_le

/-- The clamp is `1`-Lipschitz. -/
theorem abs_clamp01_sub_le (s t : ℝ) : |clamp01 s - clamp01 t| ≤ |s - t| := by
  show |max 0 (min s 1) - max 0 (min t 1)| ≤ |s - t|
  calc |max 0 (min s 1) - max 0 (min t 1)|
      ≤ max |(0 : ℝ) - 0| |min s 1 - min t 1| := abs_max_sub_max_le_max _ _ _ _
    _ = |min s 1 - min t 1| := by
        rw [sub_self, abs_zero]
        exact max_eq_right (abs_nonneg _)
    _ ≤ max |s - t| |(1 : ℝ) - 1| := abs_min_sub_min_le_max _ _ _ _
    _ = |s - t| := by
        rw [sub_self, abs_zero]
        exact max_eq_left (abs_nonneg _)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.abs_clamp01_sub_le

section Plain

variable {B : Type v} [NonUnitalCStarAlgebra B]

/-- `K - K` is bounded by every `C ≥ 0`. -/
theorem isBoundedBy_sub_self {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
    (K : Adjointable E F) {C : ℝ} (hC : 0 ≤ C) : (K.sub K).IsBoundedBy C := by
  intro x
  show F.norm (K.toFun x - K.toFun x) ≤ C * E.norm x
  rw [sub_self, F.norm_zero_vector]
  exact mul_nonneg hC (E.norm_nonneg x)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.isBoundedBy_sub_self

/-- **Norm continuity of a path of operators.** -/
def IsOpContinuous {E : CStarModule.{v, w} B} (P : ℝ → Adjointable E E) : Prop :=
  ∀ t ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ s : ℝ, |s - t| < δ → ((P s).sub (P t)).IsBoundedBy ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.IsOpContinuous

/-- The concatenation of two paths, with one formula for all times. -/
def concatPath {E : CStarModule.{v, w} B} (P Q : ℝ → Adjointable E E) (s : ℝ) :
    Adjointable E E :=
  ((P (clamp01 (2 * s))).add (Q (clamp01 (2 * s - 1)))).sub (P 1)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.concatPath

theorem concatPath_toFun {E : CStarModule.{v, w} B} (P Q : ℝ → Adjointable E E) (s : ℝ)
    (x : E.carrier) :
    (concatPath P Q s).toFun x
      = (P (clamp01 (2 * s))).toFun x + (Q (clamp01 (2 * s - 1))).toFun x - (P 1).toFun x :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.concatPath_toFun

end Plain

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **An operator path on a frame**: a norm-continuous path of Kasparov operators from `F`
to `G`. -/
def OpPath (E : CStarModule.{v, w} B) (γ : Adjointable E E) (ρ : A → Adjointable E E)
    (F G : Adjointable E E) : Prop :=
  ∃ P : ℝ → Adjointable E E, (∀ s, IsKasparovOp E γ ρ (P s)) ∧ IsOpContinuous P
    ∧ (∀ x, (P 0).toFun x = F.toFun x) ∧ (∀ x, (P 1).toFun x = G.toFun x)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OpPath

variable {E : CStarModule.{v, w} B} {γ : Adjointable E E} {ρ : A → Adjointable E E}

theorem OpPath.refl {F : Adjointable E E} (hF : IsKasparovOp E γ ρ F) : OpPath E γ ρ F F :=
  ⟨fun _ => F, fun _ => hF,
    fun _ _ hε => ⟨1, one_pos, fun _ _ => isBoundedBy_sub_self F hε.le⟩,
    fun _ => rfl, fun _ => rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OpPath.refl

theorem OpPath.symm {F G : Adjointable E E} (hp : OpPath E γ ρ F G) : OpPath E γ ρ G F := by
  obtain ⟨P, hP, hc, h0, h1⟩ := hp
  refine ⟨fun s => P (1 - s), fun s => hP (1 - s), ?_, fun x => ?_, fun x => ?_⟩
  · intro t ε hε
    obtain ⟨δ, hδ, hb⟩ := hc (1 - t) ε hε
    refine ⟨δ, hδ, fun s hs => hb (1 - s) ?_⟩
    have hst : (1 - s) - (1 - t) = -(s - t) := by ring
    rw [hst, abs_neg]
    exact hs
  · show (P (1 - 0)).toFun x = G.toFun x
    rw [sub_zero]
    exact h1 x
  · show (P (1 - 1)).toFun x = F.toFun x
    rw [sub_self]
    exact h0 x

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OpPath.symm

end KKMonoidLane
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
