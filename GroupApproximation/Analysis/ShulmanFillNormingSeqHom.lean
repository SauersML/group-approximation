import GroupApproximation.Analysis.ShulmanFillNormingDCStar

/-!
# An asymptotic lift becomes a homomorphism into the reduced product of `𝒟`s

At a fixed stage `t` a member `φ_t` of an asymptotic lift is not a
homomorphism; that is exactly why the coordinate obstruction of
`Analysis/ShulmanFillNormingResiduallyFinite` does not apply to it.  But the
whole family is a homomorphism *into the reduced product*: all four defects
vanish as `t → ∞`, so they disappear in `∏_t 𝒟 / ⨁_t 𝒟`.

`dHom` is that homomorphism, and — this is what the added unitality field
buys — it is **unital**, so it can be used as a factor map of an amalgam,
where `CStarAmalgamRepresentation` insists on `→⋆ₐ[ℂ]` rather than `→⋆ₙₐ[ℂ]`.

This is the same construction as `diagHom` of
`Analysis/ShulmanFillNormingAsymptoticMF`, without the coordinate selection:
there a single coordinate had to be chosen to reach MF models, here the whole
sequence is kept so that the `*`-strong limit map survives.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

universe u v

section SeqHom

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-- The reduced product of copies of `𝒟` along the cofinite filter. -/
abbrev DCorona : Type u :=
  CStarProductCorona
    (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)) cofinite

variable {ι hnorm hone}
variable {B : Type v} [CStarAlgebra B]
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

namespace StarStrongAsymptoticLift

/-- The `𝒟`-valued sequence of an asymptotic lift, bounded by `‖b‖`. -/
def dSeq (φ : StarStrongAsymptoticLift ι hnorm hone π) (b : B) :
    BoundedCStarSequence
      (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)) :=
  ⟨fun t ↦ ⟨φ.toFun t b, φ.mem t b⟩, memℓp_infty ⟨‖b‖, by
    rintro _ ⟨t, rfl⟩
    exact φ.norm_le t b⟩⟩

@[simp] theorem coe_dSeq_apply (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (b : B) (t : ℕ) :
    ((dSeq φ b t : StarStrong.starStrongSubalgebra ι hnorm hone) :
      StarStrong.BoundedStarSequence A) = φ.toFun t b := rfl

/-- Its class in the reduced product. -/
def dClass (φ : StarStrongAsymptoticLift ι hnorm hone π) (b : B) :
    DCorona ι hnorm hone :=
  cStarProductCoronaQuotient
    (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)) cofinite
    (dSeq φ b)

/-- **The transfer lemma for every defect.**  Two `𝒟`-valued sequences whose
underlying product-valued sequences differ by a null family have the same
class. -/
theorem dClass_eq_of_tendsto
    (u v : ℕ → StarStrong.BoundedStarSequence A)
    (x y : BoundedCStarSequence
      (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)))
    (hx : ∀ t, ((x t : StarStrong.starStrongSubalgebra ι hnorm hone) :
      StarStrong.BoundedStarSequence A) = u t)
    (hy : ∀ t, ((y t : StarStrong.starStrongSubalgebra ι hnorm hone) :
      StarStrong.BoundedStarSequence A) = v t)
    (h : Tendsto (fun t ↦ ‖u t - v t‖) atTop (𝓝 0)) :
    cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite x =
      cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite y := by
  refine cStarProductCoronaQuotient_eq_of_tendsto_norm_sub x y ?_
  refine h.congr fun t ↦ ?_
  show ‖u t - v t‖ = ‖x t - y t‖
  rw [← hx t, ← hy t]
  rfl

variable (φ : StarStrongAsymptoticLift ι hnorm hone π)

theorem dClass_one : dClass φ (1 : B) = 1 := by
  have hone' : (1 : DCorona ι hnorm hone) =
      cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite 1 :=
    (map_one (cStarProductCoronaQuotient
      (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)) cofinite)).symm
  rw [hone']
  exact dClass_eq_of_tendsto (fun t ↦ φ.toFun t 1) (fun _ ↦ 1) (dSeq φ 1) 1
    (fun _ ↦ rfl) (fun _ ↦ rfl) φ.tendsto_one

theorem dClass_zero : dClass φ (0 : B) = 0 := by
  have hz : Tendsto (fun t ↦ ‖φ.toFun t (0 : B) -
      (0 : StarStrong.BoundedStarSequence A)‖) atTop (𝓝 0) := by
    have hfun : (fun t ↦ ‖φ.toFun t (0 : B) -
        (0 : StarStrong.BoundedStarSequence A)‖) = fun _ : ℕ ↦ (0 : ℝ) := by
      funext t
      rw [toFun_zero φ t, sub_zero, norm_zero]
    rw [hfun]
    exact tendsto_const_nhds
  have hzero' : (0 : DCorona ι hnorm hone) =
      cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite 0 :=
    (map_zero (cStarProductCoronaQuotient
      (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)) cofinite)).symm
  rw [hzero']
  exact dClass_eq_of_tendsto (fun t ↦ φ.toFun t 0) (fun _ ↦ 0) (dSeq φ 0) 0
    (fun _ ↦ rfl) (fun _ ↦ rfl) hz

theorem dClass_smul (z : ℂ) (b : B) : dClass φ (z • b) = z • dClass φ b := by
  have hsmul : z • dClass φ b =
      cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite (z • dSeq φ b) :=
    (map_smul (cStarProductCoronaQuotient
      (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)) cofinite)
      z (dSeq φ b)).symm
  rw [hsmul]
  exact dClass_eq_of_tendsto (fun t ↦ φ.toFun t (z • b))
    (fun t ↦ z • φ.toFun t b) (dSeq φ (z • b)) (z • dSeq φ b)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (φ.tendsto_smul z b)

theorem dClass_add (b c : B) :
    dClass φ (b + c) = dClass φ b + dClass φ c := by
  have hz : Tendsto
      (fun t ↦ ‖φ.toFun t (b + c) - (φ.toFun t b + φ.toFun t c)‖)
      atTop (𝓝 0) := by
    simpa only [sub_add_eq_sub_sub] using φ.tendsto_add b c
  have hadd : dClass φ b + dClass φ c =
      cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite (dSeq φ b + dSeq φ c) :=
    (map_add (cStarProductCoronaQuotient
      (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone)) cofinite)
      (dSeq φ b) (dSeq φ c)).symm
  rw [hadd]
  exact dClass_eq_of_tendsto (fun t ↦ φ.toFun t (b + c))
    (fun t ↦ φ.toFun t b + φ.toFun t c) (dSeq φ (b + c)) (dSeq φ b + dSeq φ c)
    (fun _ ↦ rfl) (fun _ ↦ rfl) hz

theorem dClass_mul (b c : B) :
    dClass φ (b * c) = dClass φ b * dClass φ c := by
  have hmul : dClass φ b * dClass φ c =
      cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite (dSeq φ b * dSeq φ c) := (map_mul _ _ _).symm
  rw [hmul]
  exact dClass_eq_of_tendsto (fun t ↦ φ.toFun t (b * c))
    (fun t ↦ φ.toFun t b * φ.toFun t c) (dSeq φ (b * c)) (dSeq φ b * dSeq φ c)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (φ.tendsto_mul b c)

theorem dClass_star (b : B) : dClass φ (star b) = star (dClass φ b) := by
  have hstar : star (dClass φ b) =
      cStarProductCoronaQuotient
        (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
        cofinite (star (dSeq φ b)) := (map_star _ _).symm
  rw [hstar]
  exact dClass_eq_of_tendsto (fun t ↦ φ.toFun t (star b))
    (fun t ↦ star (φ.toFun t b)) (dSeq φ (star b)) (star (dSeq φ b))
    (fun _ ↦ rfl) (fun _ ↦ rfl) (φ.tendsto_star b)

/-- **The asymptotic lift, as a unital `*`-homomorphism into `∏_t 𝒟 / ⨁_t 𝒟`.**
Every defect vanishes as `t → ∞`, so it vanishes in the reduced product; the
unitality field makes the map unital, which is what an amalgam factor map has
to be. -/
def dHom : B →⋆ₐ[ℂ] DCorona ι hnorm hone where
  toFun := dClass φ
  map_one' := dClass_one φ
  map_mul' := dClass_mul φ
  map_zero' := dClass_zero φ
  map_add' := dClass_add φ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      dClass_smul φ r 1, dClass_one φ]
  map_star' := dClass_star φ

@[simp] theorem dHom_apply (b : B) : dHom φ b = dClass φ b := rfl

end StarStrongAsymptoticLift

end SeqHom

end

end ShulmanFill
end GroupApproximation
