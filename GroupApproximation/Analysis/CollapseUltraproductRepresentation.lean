import GroupApproximation.Analysis.CollapseCocycleAnalytic
import GroupApproximation.Analysis.CollapseDelormeEndpoint
import GroupApproximation.Analysis.OmegaHilbertComplete

/-!
# `π` as a unitary representation on `K_ω`, and `CO.21b` inside it

Proof-ledger row `CO.21b`.  The printed proof of `thm:projection-collapse`
says, of the conjugation action on the rank-normalized ultraproduct,

> Conjugation by a unitary preserves each `⟨·,·⟩_n` … so
> `π(h) = [Ad U_n(h)]_ω` defines a unitary representation of `H` on `K_ω`

and then feeds `π` to Delorme–Guichardet.  `Analysis/CollapseCocycleAnalytic`
built `Ad U_n` as a linear endomorphism `conjQ` of the ultraproduct and proved
its two representation properties separately — norm preservation
(`norm_mkK_conjBounded`) and multiplicativity (`conjBounded_comp`,
`conjBounded_one`).  What was missing was the *bundle*: a genuine
`H →* (K_ω ≃ₗᵢ[ℂ] K_ω)`, which is the shape Delorme consumes.  This file
supplies it, and then states the printed contradiction inside `K_ω`.

The inverse is the only new mathematical ingredient, and it is the adjoint
family: `starFam` sends `U_n` to `U_n*`, and the two unitarity identities
`U U* = 1` and `U* U = 1` turn `conjBounded_comp` and `conjBounded_one` into
the two round trips.  `LinearEquiv.ofLinear` then packages `conjQ` and its
inverse.  Every step that has to descend to the quotient does so by picking a
representative with `Submodule.Quotient.mk_surjective`, the idiom
`Analysis/VectorHilbertUltraproduct` already uses on this same construction.

`collapse_contradiction_kOmega` is the payoff: the printed last paragraph of
the collapse proof, stated for the rank-normalized ultraproduct, with

* Delorme–Guichardet **proved**, not cited — via
  `CollapseDelormeEndpoint.exists_primitive_of_hasKazhdanPropertyT`, which
  runs `Kazhdan/DelormeFixedPoint` through `Kazhdan/KazhdanComplex.realifyHom`;
* completeness of `K_ω` **proved**, not assumed — the instance
  `Analysis/OmegaHilbertComplete.kOmegaCompleteSpace` is found by typeclass
  search, which is why no `CompleteSpace` hypothesis appears below;
* `π` **built**, not hypothesised — `conjRep`.

One hypothesis remains, `htransport`: the identification of
`Fix π(sLs⁻¹)` with `Fix π(L)`.  The weighted transport theorem is invoked at
`ν_n = k_n` in `Sofic/CollapseRankWeightTransport`; the missing passage is
from that transported *commutant* statement to the equality of fixed
subspaces, which is where the printed `P ≤ Q`, `P ∼ Q`, finiteness argument
lives.

`Θ` is taken exactly multiplicative here.  The printed lift of `lem:unitarycorona`
is only asymptotically multiplicative, and upgrading `conjRep` to accept such
a lift is a separate step, not attempted here.
-/

namespace GroupApproximation
namespace CollapseUltraproductRepresentation

open Filter Matrix Topology
open ScaledKazhdanTransport UltraproductModelConstruction
open RankNormalizedHilbertization KOmegaHilbert CollapseCocycleAnalytic
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (ω : Ultrafilter ℕ)

/-! ## The adjoint family -/

/-- The adjoint coordinate family `U*_n`, which implements the inverse of
`Ad U_n`. -/
def starFam (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    ∀ n, Matrix.unitaryGroup (Y n) ℂ := fun n ↦ star (U n)

theorem mul_starFam (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    (fun n ↦ U n * starFam Y U n)
      = fun n ↦ (1 : Matrix.unitaryGroup (Y n) ℂ) := by
  funext n
  apply Subtype.ext
  exact (U n).2.2

theorem starFam_mul (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    (fun n ↦ starFam Y U n * U n)
      = fun n ↦ (1 : Matrix.unitaryGroup (Y n) ℂ) := by
  funext n
  apply Subtype.ext
  exact (U n).2.1

/-! ## The two round trips -/

theorem conjBounded_starFam_left (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ)
    (ξ : massBounded Y w) :
    conjBounded Y w U (conjBounded Y w (starFam Y U) ξ) = ξ := by
  rw [conjBounded_comp, mul_starFam, conjBounded_one]

theorem conjBounded_starFam_right (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ)
    (ξ : massBounded Y w) :
    conjBounded Y w (starFam Y U) (conjBounded Y w U ξ) = ξ := by
  rw [conjBounded_comp, starFam_mul, conjBounded_one]

theorem conjQ_comp_starFam (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    (conjQ Y w ω U).comp (conjQ Y w ω (starFam Y U)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
  show conjQ Y w ω U (conjQ Y w ω (starFam Y U) (Submodule.Quotient.mk ξ))
    = Submodule.Quotient.mk ξ
  rw [conjQ_mk, conjQ_mk, conjBounded_starFam_left]

theorem conjQ_starFam_comp (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    (conjQ Y w ω (starFam Y U)).comp (conjQ Y w ω U) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
  show conjQ Y w ω (starFam Y U) (conjQ Y w ω U (Submodule.Quotient.mk ξ))
    = Submodule.Quotient.mk ξ
  rw [conjQ_mk, conjQ_mk, conjBounded_starFam_right]

/-! ## `π(u)` as a unitary of `K_ω` -/

/-- `Ad U_n` as a linear automorphism of the ultraproduct. -/
def conjLinearEquiv (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    Vec Y w ω ≃ₗ[ℂ] Vec Y w ω :=
  LinearEquiv.ofLinear (conjQ Y w ω U) (conjQ Y w ω (starFam Y U))
    (conjQ_comp_starFam Y w ω U) (conjQ_starFam_comp Y w ω U)

/-- **`π(h) = [Ad U_n(h)]_ω`**, as a unitary of `K_ω`: linear, invertible, and
norm preserving because unitary conjugation is mass exact. -/
def conjIsometryEquiv (hw : ∀ n, 0 ≤ w n)
    (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    KOmega Y w ω hw ≃ₗᵢ[ℂ] KOmega Y w ω hw where
  toLinearEquiv := conjLinearEquiv Y w ω U
  norm_map' := by
    intro x
    obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
    exact norm_mkK_conjBounded Y w ω hw U ξ

@[simp] theorem conjIsometryEquiv_mk (hw : ∀ n, 0 ≤ w n)
    (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) (ξ : massBounded Y w) :
    conjIsometryEquiv Y w ω hw U (mkK Y w ω hw ξ)
      = mkK Y w ω hw (conjBounded Y w U ξ) := rfl

/-! ## `π` as a representation -/

/-- **The conjugation representation of `H` on `K_ω`.**  This is the printed
*"`π(h) = [Ad U_n(h)]_ω` defines a unitary representation of `H` on `K_ω`"*,
for a coordinatewise unitary lift `Θ` that is exactly multiplicative. -/
def conjRep {H : Type u} [Group H] (hw : ∀ n, 0 ≤ w n)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) :
    H →* (KOmega Y w ω hw ≃ₗᵢ[ℂ] KOmega Y w ω hw) where
  toFun g := conjIsometryEquiv Y w ω hw (fun n ↦ Θ g n)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
    have h1 : (fun n ↦ Θ (1 : H) n)
        = fun n ↦ (1 : Matrix.unitaryGroup (Y n) ℂ) := by
      funext n
      exact congrArg (fun V : (∀ m, Matrix.unitaryGroup (Y m) ℂ) ↦ V n)
        (map_one Θ)
    show Submodule.Quotient.mk (conjBounded Y w (fun n ↦ Θ (1 : H) n) ξ)
      = Submodule.Quotient.mk ξ
    rw [h1, conjBounded_one]
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
    have h2 : (fun n ↦ Θ (g * h) n) = fun n ↦ Θ g n * Θ h n := by
      funext n
      exact congrArg (fun V : (∀ m, Matrix.unitaryGroup (Y m) ℂ) ↦ V n)
        (map_mul Θ g h)
    show Submodule.Quotient.mk (conjBounded Y w (fun n ↦ Θ (g * h) n) ξ)
      = Submodule.Quotient.mk
          (conjBounded Y w (fun n ↦ Θ g n)
            (conjBounded Y w (fun n ↦ Θ h n) ξ))
    calc Submodule.Quotient.mk (conjBounded Y w (fun n ↦ Θ (g * h) n) ξ)
        = Submodule.Quotient.mk
            (conjBounded Y w (fun n ↦ Θ g n * Θ h n) ξ) := by rw [h2]
      _ = Submodule.Quotient.mk
            (conjBounded Y w (fun n ↦ Θ g n)
              (conjBounded Y w (fun n ↦ Θ h n) ξ)) := by
            rw [conjBounded_comp]

/-! ## `CO.21b` inside `K_ω` -/

/-- **The printed contradiction, inside the rank-normalized ultraproduct.**

Delorme–Guichardet is proved rather than cited, completeness of `K_ω` is
found by typeclass search from `Analysis/OmegaHilbertComplete`, and `π` is
the representation built above.  The single remaining hypothesis is
`htransport`, the identification of `Fix π(sLs⁻¹)` with `Fix π(L)` that the
weighted transport theorem at `ν_n = k_n` is meant to supply. -/
theorem collapse_contradiction_kOmega {H : Type u} [Group H]
    (hw : ∀ n, 0 ≤ w n) (hT : HasKazhdanPropertyT.{u, u} H)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (β : H → KOmega Y w ω hw) (c : H → H)
    (hβ : ∀ g h : H,
      β (g * h) = β g + conjRep Y w ω hw Θ g (β h))
    (hcompressed : ∀ a : H, β (c a) = 0)
    (htransport : ∀ y : KOmega Y w ω hw,
      (∀ a : H, conjRep Y w ω hw Θ (c a) y = y) →
        ∀ g : H, conjRep Y w ω hw Θ g y = y)
    (hne : ∃ g : H, β g ≠ 0) : False :=
  CollapseDelormeEndpoint.collapse_contradiction_of_hasKazhdanPropertyT hT
    (conjRep Y w ω hw Θ) β c hβ hcompressed htransport hne

end

end CollapseUltraproductRepresentation
end GroupApproximation
