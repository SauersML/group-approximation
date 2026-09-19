import GroupApproximation.Analysis.CStarProductCorona

/-!
# Product-corona core for tensor synchronization

This module isolates the passage from coordinatewise unitary data to the
C-star product corona.  It packages bounded unitary sequences, their corona
classes, the induced group homomorphism, and descent of exact coordinate
covariance.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

open PolarLiftingGeneralCStar Filter

noncomputable section

universe u v w

/-- A coordinatewise unitary family is a bounded C-star sequence. -/
def boundedUnitaryCStarSequence
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) : BoundedCStarSequence B :=
  ⟨fun n ↦ (U n : B n), memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact le_of_eq (CStarRing.norm_of_mem_unitary (U n).property)⟩⟩

@[simp] theorem boundedUnitaryCStarSequence_apply
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) (n : ℕ) :
    boundedUnitaryCStarSequence B U n = (U n : B n) :=
  rfl

/-- The class of a coordinatewise unitary family in the reduced product. -/
def unitaryCStarSequenceToProductCorona
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) :
    unitary (CStarProductCorona B cofinite) := by
  let q := cStarProductCoronaQuotient B cofinite
  let a := boundedUnitaryCStarSequence B U
  refine ⟨q a, ?_⟩
  constructor
  · calc
      star (q a) * q a = q (star a * a) := by rw [← map_star, ← map_mul]
      _ = q 1 := by
        congr 1
        apply lp.ext
        funext n
        exact (U n).property.1
      _ = 1 := map_one q
  · calc
      q a * star (q a) = q (a * star a) := by rw [← map_star, ← map_mul]
      _ = q 1 := by
        congr 1
        apply lp.ext
        funext n
        exact (U n).property.2
      _ = 1 := map_one q

@[simp] theorem coe_unitaryCStarSequenceToProductCorona
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) :
    (unitaryCStarSequenceToProductCorona B U : CStarProductCorona B cofinite) =
      cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B U) :=
  rfl

/-- Exact coordinate homomorphisms assemble into a homomorphism to the
unitary group of the C-star reduced product. -/
def coordinateProductCoronaHom
    {G : Type w} [Group G]
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (V : ∀ n, G →* unitary (B n)) :
    G →* unitary (CStarProductCorona B cofinite) where
  toFun g := unitaryCStarSequenceToProductCorona B (fun n ↦ V n g)
  map_one' := by
    apply Subtype.ext
    change cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B (fun n ↦ V n 1)) = 1
    rw [← map_one (cStarProductCoronaQuotient B cofinite)]
    congr 1
    apply lp.ext
    funext n
    exact congrArg Subtype.val (map_one (V n))
  map_mul' g h := by
    apply Subtype.ext
    change cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B (fun n ↦ V n (g * h))) =
      cStarProductCoronaQuotient B cofinite
          (boundedUnitaryCStarSequence B (fun n ↦ V n g)) *
        cStarProductCoronaQuotient B cofinite
          (boundedUnitaryCStarSequence B (fun n ↦ V n h))
    rw [← map_mul]
    congr 1
    apply lp.ext
    funext n
    exact congrArg Subtype.val (map_mul (V n) g h)

/-- Coordinate covariance descends verbatim to covariance in the C-star
product corona. -/
theorem productCorona_covariance_of_coordinate
    {G : Type w} [Group G] {S : Type v} [Group S]
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (V : ∀ n, G →* unitary (B n))
    (source target : S →* G) (W : ∀ n, unitary (B n))
    (hcov : ∀ (n : ℕ) (s : S),
      (W n : B n) * (V n (source s) : B n) * star (W n : B n) =
        (V n (target s) : B n)) :
    let Vbar := coordinateProductCoronaHom B V
    let Wbar := unitaryCStarSequenceToProductCorona B W
    ∀ s : S,
      (Wbar : CStarProductCorona B cofinite) *
          (Vbar (source s) : CStarProductCorona B cofinite) *
            star (Wbar : CStarProductCorona B cofinite) =
        (Vbar (target s) : CStarProductCorona B cofinite) := by
  intro Vbar Wbar s
  change cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B W) *
      cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B (fun n ↦ V n (source s))) *
      star (cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B W)) =
    cStarProductCoronaQuotient B cofinite
      (boundedUnitaryCStarSequence B (fun n ↦ V n (target s)))
  rw [← map_star, ← map_mul, ← map_mul]
  congr 1
  apply lp.ext
  funext n
  exact hcov n s

end

end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
