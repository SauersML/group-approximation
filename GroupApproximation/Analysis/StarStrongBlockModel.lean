import GroupApproximation.Analysis.ArvesonBHTarget
import GroupApproximation.Analysis.StarStrongMatrixSequencesAlgebra

/-!
# The block model: matrix algebras inside `B(H)` along a family of isometries

Shulman's algebra `𝒟` is built in `Analysis/StarStrongMatrixSequencesAlgebra`
from data `(ι, hnorm, hone)`: contractive `*`-homomorphisms `ι n : A n → B(H)`
with `ι n (1) → 1` strongly.  Nothing in the repository supplied that data, so
`𝒟` was an empty construction; the printed instance is `A n = M_{kₙ}` acting on
the first `kₙ` coordinates of `ℓ²`.

This module reduces the whole of that instance to *one* piece of concrete data:
a family of isometries

    `J n : ℂ^{kₙ} → H`  with  `Jₙ* Jₙ = 1`, `‖Jₙ‖ ≤ 1`, `Jₙ Jₙ* → 1` strongly.

Given it, `blockHom` below is the `*`-homomorphism `B(ℂ^{kₙ}) → B(H)`, `T ↦ Jₙ T
Jₙ*`, and the three hypotheses of `𝒟` come out:

* `blockHom` is multiplicative because `Jₙ* Jₙ = 1` cancels in the middle;
* it is contractive because `‖Jₙ‖ ≤ 1` and the adjoint is isometric;
* `blockHom (1) = Jₙ Jₙ*`, so `hone` *is* the strong convergence `Jₙ Jₙ* → 1`.

So the model is not an analytic construction at all once the isometries exist:
it is the same transport `Analysis/ArvesonBHTarget` uses, with its unit and
product clauses added.  The same family is what `arvesonBH_of_limit` takes as
data, so one construction serves both.

## The one concrete input, and where it is built

`EllTwoBlockFamilyStatement` is the existence of that family on `ℓ²` at
`kₙ = n`.  `Analysis/EllTwoBlockFamily` proves it: `J n x = ∑ i, lp.single 2 i
(x i)`, a finite sum of point masses, with its adjoint the restriction to the
first `n` coordinates and the strong convergence read off `lp.hasSum_single`.

An earlier version of this paragraph said the family was left unbuilt because
`lp.single_add`, `lp.inner_single_left` and `lp.hasSum_single` had no precedent
in this repository.  That was wrong about the last two: `lp.inner_single_left`
is used in six modules and `lp.hasSum_single` in three, along with
`lp.evalCLM`, `lp.single_apply_self`, `lp.single_apply_ne`, `lp.norm_single`
and `PiLp.inner_apply`.  Only `lp.single_add` is genuinely absent, and
`EllTwoBlockFamily` proves it coordinatewise instead of assuming it.  The
lesson is that "no precedent" is a claim about a search, and that search was
too narrow.

Everything above the family is proved here, so the whole `𝒟` instance and the
isometry data of `Analysis/ArvesonBHTarget` rest on that one construction.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace StarStrong

open Filter Topology

open scoped InnerProductSpace

noncomputable section

section Block

variable {E F : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The block homomorphism** `T ↦ J T J*` of an isometry `J : F → E`.  It is a
`*`-homomorphism, not merely linear: multiplicativity is exactly the
cancellation `J* J = 1`. -/
def blockHom (J : F →L[ℂ] E)
    (hJ : ∀ v : F, (ContinuousLinearMap.adjoint J) (J v) = v) :
    (F →L[ℂ] F) →⋆ₙₐ[ℂ] (E →L[ℂ] E) where
  toFun T := J.comp (T.comp (ContinuousLinearMap.adjoint J))
  map_zero' := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show J ((0 : F →L[ℂ] F) ((ContinuousLinearMap.adjoint J) v)) = 0
    show J (0 : F) = 0
    exact map_zero J
  map_add' S T := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show J ((S + T) ((ContinuousLinearMap.adjoint J) v))
      = J (S ((ContinuousLinearMap.adjoint J) v))
        + J (T ((ContinuousLinearMap.adjoint J) v))
    show J (S ((ContinuousLinearMap.adjoint J) v)
        + T ((ContinuousLinearMap.adjoint J) v))
      = J (S ((ContinuousLinearMap.adjoint J) v))
        + J (T ((ContinuousLinearMap.adjoint J) v))
    rw [map_add]
  map_smul' z T := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show J ((z • T) ((ContinuousLinearMap.adjoint J) v))
      = z • J (T ((ContinuousLinearMap.adjoint J) v))
    show J (z • (T ((ContinuousLinearMap.adjoint J) v)))
      = z • J (T ((ContinuousLinearMap.adjoint J) v))
    rw [map_smul]
  map_mul' S T := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show J (S (T ((ContinuousLinearMap.adjoint J) v)))
      = J (S ((ContinuousLinearMap.adjoint J)
          (J (T ((ContinuousLinearMap.adjoint J) v)))))
    rw [hJ]
  map_star' T := by
    symm
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have hleft : ⟪J (T ((ContinuousLinearMap.adjoint J) x)), y⟫_ℂ
        = ⟪T ((ContinuousLinearMap.adjoint J) x),
            (ContinuousLinearMap.adjoint J) y⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right J
        (T ((ContinuousLinearMap.adjoint J) x)) y).symm
    have hright : ⟪x, J ((star T) ((ContinuousLinearMap.adjoint J) y))⟫_ℂ
        = ⟪(ContinuousLinearMap.adjoint J) x,
            (star T) ((ContinuousLinearMap.adjoint J) y)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left J
        ((star T) ((ContinuousLinearMap.adjoint J) y)) x).symm
    have hmid : ⟪T ((ContinuousLinearMap.adjoint J) x),
          (ContinuousLinearMap.adjoint J) y⟫_ℂ
        = ⟪(ContinuousLinearMap.adjoint J) x,
            (star T) ((ContinuousLinearMap.adjoint J) y)⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact (ContinuousLinearMap.adjoint_inner_right T
        ((ContinuousLinearMap.adjoint J) x)
        ((ContinuousLinearMap.adjoint J) y)).symm
    show ⟪J (T ((ContinuousLinearMap.adjoint J) x)), y⟫_ℂ
      = ⟪x, J ((star T) ((ContinuousLinearMap.adjoint J) y))⟫_ℂ
    rw [hleft, hright, hmid]

@[simp] theorem blockHom_apply (J : F →L[ℂ] E)
    (hJ : ∀ v : F, (ContinuousLinearMap.adjoint J) (J v) = v)
    (T : F →L[ℂ] F) (v : E) :
    blockHom J hJ T v = J (T ((ContinuousLinearMap.adjoint J) v)) := rfl

/-- The block homomorphism of a contraction is contractive. -/
theorem norm_blockHom_le (J : F →L[ℂ] E)
    (hJ : ∀ v : F, (ContinuousLinearMap.adjoint J) (J v) = v)
    (hJnorm : ‖J‖ ≤ 1) (T : F →L[ℂ] F) : ‖blockHom J hJ T‖ ≤ ‖T‖ := by
  have hadj : ‖(ContinuousLinearMap.adjoint J : E →L[ℂ] F)‖ = ‖J‖ :=
    ContinuousLinearMap.adjoint.norm_map J
  have h1 : ‖blockHom J hJ T‖
      ≤ ‖J‖ * ‖T.comp (ContinuousLinearMap.adjoint J)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h2 : ‖T.comp (ContinuousLinearMap.adjoint J)‖
      ≤ ‖T‖ * ‖(ContinuousLinearMap.adjoint J : E →L[ℂ] F)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h3 : ‖T.comp (ContinuousLinearMap.adjoint J)‖ ≤ ‖T‖ := by
    rw [hadj] at h2
    nlinarith [norm_nonneg T, norm_nonneg J, h2, hJnorm]
  nlinarith [norm_nonneg J, norm_nonneg T,
    norm_nonneg (T.comp (ContinuousLinearMap.adjoint J)), h1, h3, hJnorm]

/-- The block homomorphism sends the unit to the range projection. -/
theorem blockHom_one (J : F →L[ℂ] E)
    (hJ : ∀ v : F, (ContinuousLinearMap.adjoint J) (J v) = v) (v : E) :
    blockHom J hJ 1 v = J ((ContinuousLinearMap.adjoint J) v) := rfl

end Block

/-! ## The data `𝒟` needs, and the reduction to it -/

section Family

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {k : ℕ → ℕ}
variable (J : ∀ n, EuclideanSpace ℂ (Fin (k n)) →L[ℂ] E)
variable (hJ : ∀ (n : ℕ) (v : EuclideanSpace ℂ (Fin (k n))),
  (ContinuousLinearMap.adjoint (J n)) (J n v) = v)

/-- The family of block homomorphisms, as the `ι` of `𝒟`. -/
def blockIota :
    ∀ n, (EuclideanSpace ℂ (Fin (k n)) →L[ℂ] EuclideanSpace ℂ (Fin (k n)))
      →⋆ₙₐ[ℂ] (E →L[ℂ] E) :=
  fun n ↦ blockHom (J n) (hJ n)

/-- `hnorm` for the block family. -/
theorem norm_blockIota_le (hJnorm : ∀ n, ‖J n‖ ≤ 1) (n : ℕ)
    (T : EuclideanSpace ℂ (Fin (k n)) →L[ℂ] EuclideanSpace ℂ (Fin (k n))) :
    ‖blockIota J hJ n T‖ ≤ ‖T‖ :=
  norm_blockHom_le (J n) (hJ n) (hJnorm n) T

/-- `hone` for the block family: it *is* the strong convergence of the range
projections `Jₙ Jₙ*` to `1`. -/
theorem tendsto_blockIota_one
    (hP : ∀ v : E,
      Tendsto (fun n ↦ (J n) ((ContinuousLinearMap.adjoint (J n)) v))
        atTop (𝓝 v))
    (v : E) :
    Tendsto (fun n ↦ blockIota J hJ n 1 v) atTop (𝓝 v) :=
  hP v

end Family

/-! ## The one concrete input -/

/-- **The block family on `ℓ²`.**  The isometries of the first `n` coordinates,
with their range projections tending strongly to `1`.  This is the only
concrete input the whole `𝒟` instance needs, and the same data
`Analysis/ArvesonBHTarget.arvesonBH_of_limit` takes.

Left as a statement: building it is `J n x = ∑ i, lp.single 2 i (x i)` together
with its adjoint and the strong convergence, and the `lp` lemmas that
computation needs have no precedent in this repository. -/
def EllTwoBlockFamilyStatement : Prop :=
  ∃ J : ∀ n : ℕ,
      EuclideanSpace ℂ (Fin n) →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2,
    (∀ (n : ℕ) (v : EuclideanSpace ℂ (Fin n)),
        (ContinuousLinearMap.adjoint (J n)) (J n v) = v) ∧
      (∀ n : ℕ, ‖J n‖ ≤ 1) ∧
        ∀ v : lp (fun _ : ℕ ↦ ℂ) 2,
          Tendsto (fun n ↦ (J n) ((ContinuousLinearMap.adjoint (J n)) v))
            atTop (𝓝 v)

end

end StarStrong
end GroupApproximation
