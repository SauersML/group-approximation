import GroupApproximation.Analysis.LanceMatrixArveson
import GroupApproximation.Analysis.CStarCompletelyPositiveForm

/-!
# Arveson's extension theorem at a `B(H)` target, reduced to the limit step

`Analysis/LanceMatrixArveson.exists_ucp_extension` proves Arveson's theorem when
the target is `B(ℂᵏ)`.  Enders--Shulman's proof of Theorem 4.11, and so
`Analysis/ShulmanFillTheorem13`, needs it at a `B(H)` target.  The classical
passage is:

1. compress `Φ` by an isometry `Jₙ : ℂ^{kₙ} → H`, giving a unital form-positive
   map into `B(ℂ^{kₙ})`;
2. extend that by the matrix case;
3. dilate the extension back to `H`, giving `Ψₙ : A → B(H)`, form-positive, with
   `Ψₙ(1) = Pₙ = Jₙ Jₙ*` and `Ψₙ|_C = Pₙ Φ(·) Pₙ`;
4. take a point-weak\* cluster point of `(Ψₙ)`.

Steps 1--3 are proved here.  They are exactly the algebra of an isometry, and
need nothing about `H` beyond completeness:

    `⟪v, J* T (J w)⟫ = ⟪J v, T (J w)⟫` and `⟪v, J S (J* w)⟫ = ⟪J* v, S (J* w)⟫` ,

so a form-positivity sum for the transported map is a form-positivity sum for
the original one at the transported vectors.  Note that the *dilation* is not
unital — `Ψₙ(1) = Pₙ`, not `1` — and that is why unitality of the extension can
only appear in the limit.

Step 4 is *not* proved here.  It is the one place where a limit of operators has
to be produced, and the standard construction — an ultrafilter limit of the
matrix coefficients `⟪v, Ψₙ(x) w⟫`, bounded because a form-positive map with
`Ψₙ(1) ≤ 1` is contractive, followed by the Riesz correspondence between bounded
sesquilinear forms and operators — needs an API this repository has no precedent
for.  It is recorded below as the single named `Prop` `ArvesonLimitStatement`,
and `arvesonBH_of_limit` proves Arveson at a `B(H)` target from it together with
steps 1--3.

The exhausting family `Jₙ` is taken as *data*, not asserted to exist: in the
printed setting `H = ℓ²` and `Jₙ` is the inclusion of the first `kₙ`
coordinates, which is what the concrete model `M_n ↪ B(ℓ²)` will supply.  The
two weak-convergence hypotheses are what `Pₙ → 1` strongly gives.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.  Every Mathlib name it uses has a
precedent in the tree: `ContinuousLinearMap.adjoint_inner_left` and
`adjoint_inner_right`, `star_eq_adjoint`, `eq_adjoint_iff`.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

open Filter Topology

noncomputable section

/-! ## Form positivity -/

variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]

/-- **Complete positivity in the form sense**, the shape
`LanceMatrixArveson.exists_ucp_extension` consumes, named once so that it can be
transported along an isometry. -/
def IsFormCP {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Φ : B →ₗ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ (m : ℕ) (a : Fin m → B) (v : Fin m → K),
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, ⟪v i, Φ (star (a i) * a j) (v j)⟫_ℂ).re

/-- A completely positive map is form positive.  The empty tuple is the one case
`IsCompletelyPositive.form_nonneg` does not cover, and there the sum is zero. -/
theorem isFormCP_of_isCompletelyPositive {A : Type} [CStarAlgebra A]
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {Θ : A →ₗ[ℂ] (K →L[ℂ] K)} (hΘ : IsCompletelyPositive Θ) : IsFormCP Θ := by
  intro m a v
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · haveI : NeZero m := ⟨by omega⟩
    exact (hΘ.form_nonneg a v).1

/-! ## Compression and dilation along an isometry -/

section Transport

variable {H K : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `J* Φ(·) J`, the compression of a map into `B(H)` to a map into `B(K)`. -/
def isometryCompress (J : K →L[ℂ] H) (Φ : B →ₗ[ℂ] (H →L[ℂ] H)) :
    B →ₗ[ℂ] (K →L[ℂ] K) where
  toFun b := (ContinuousLinearMap.adjoint J).comp ((Φ b).comp J)
  map_add' b b' := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show (ContinuousLinearMap.adjoint J) ((Φ (b + b')) (J v))
      = (ContinuousLinearMap.adjoint J) ((Φ b) (J v))
        + (ContinuousLinearMap.adjoint J) ((Φ b') (J v))
    rw [Φ.map_add]
    show (ContinuousLinearMap.adjoint J) ((Φ b) (J v) + (Φ b') (J v))
      = (ContinuousLinearMap.adjoint J) ((Φ b) (J v))
        + (ContinuousLinearMap.adjoint J) ((Φ b') (J v))
    rw [map_add]
  map_smul' z b := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show (ContinuousLinearMap.adjoint J) ((Φ (z • b)) (J v))
      = z • (ContinuousLinearMap.adjoint J) ((Φ b) (J v))
    rw [Φ.map_smul]
    show (ContinuousLinearMap.adjoint J) (z • ((Φ b) (J v)))
      = z • (ContinuousLinearMap.adjoint J) ((Φ b) (J v))
    rw [map_smul]

@[simp] theorem isometryCompress_apply (J : K →L[ℂ] H)
    (Φ : B →ₗ[ℂ] (H →L[ℂ] H)) (b : B) (v : K) :
    isometryCompress J Φ b v =
      (ContinuousLinearMap.adjoint J) ((Φ b) (J v)) := rfl

/-- `J Θ(·) J*`, the dilation of a map into `B(K)` to a map into `B(H)`. -/
def isometryDilate (J : K →L[ℂ] H) (Θ : B →ₗ[ℂ] (K →L[ℂ] K)) :
    B →ₗ[ℂ] (H →L[ℂ] H) where
  toFun b := J.comp ((Θ b).comp (ContinuousLinearMap.adjoint J))
  map_add' b b' := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show J ((Θ (b + b')) ((ContinuousLinearMap.adjoint J) v))
      = J ((Θ b) ((ContinuousLinearMap.adjoint J) v))
        + J ((Θ b') ((ContinuousLinearMap.adjoint J) v))
    rw [Θ.map_add]
    show J ((Θ b) ((ContinuousLinearMap.adjoint J) v)
        + (Θ b') ((ContinuousLinearMap.adjoint J) v))
      = J ((Θ b) ((ContinuousLinearMap.adjoint J) v))
        + J ((Θ b') ((ContinuousLinearMap.adjoint J) v))
    rw [map_add]
  map_smul' z b := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    show J ((Θ (z • b)) ((ContinuousLinearMap.adjoint J) v))
      = z • J ((Θ b) ((ContinuousLinearMap.adjoint J) v))
    rw [Θ.map_smul]
    show J (z • ((Θ b) ((ContinuousLinearMap.adjoint J) v)))
      = z • J ((Θ b) ((ContinuousLinearMap.adjoint J) v))
    rw [map_smul]

@[simp] theorem isometryDilate_apply (J : K →L[ℂ] H)
    (Θ : B →ₗ[ℂ] (K →L[ℂ] K)) (b : B) (v : H) :
    isometryDilate J Θ b v =
      J ((Θ b) ((ContinuousLinearMap.adjoint J) v)) := rfl

/-! ## What the transport preserves -/

/-- Form positivity survives compression: the sum for `J* Φ(·) J` at `v` is the
sum for `Φ` at `J ∘ v`. -/
theorem isFormCP_isometryCompress (J : K →L[ℂ] H) (Φ : B →ₗ[ℂ] (H →L[ℂ] H))
    (hΦ : IsFormCP Φ) : IsFormCP (isometryCompress J Φ) := by
  intro m a v
  have hterm : ∀ i j : Fin m,
      ⟪v i, isometryCompress J Φ (star (a i) * a j) (v j)⟫_ℂ
        = ⟪J (v i), Φ (star (a i) * a j) (J (v j))⟫_ℂ := by
    intro i j
    rw [isometryCompress_apply]
    exact ContinuousLinearMap.adjoint_inner_right J (v i)
      ((Φ (star (a i) * a j)) (J (v j)))
  simp only [hterm]
  exact hΦ m a fun i ↦ J (v i)

/-- Form positivity survives dilation, by the same computation at `J*`. -/
theorem isFormCP_isometryDilate (J : K →L[ℂ] H) (Θ : B →ₗ[ℂ] (K →L[ℂ] K))
    (hΘ : IsFormCP Θ) : IsFormCP (isometryDilate J Θ) := by
  intro m a v
  have hterm : ∀ i j : Fin m,
      ⟪v i, isometryDilate J Θ (star (a i) * a j) (v j)⟫_ℂ
        = ⟪(ContinuousLinearMap.adjoint J) (v i),
            Θ (star (a i) * a j)
              ((ContinuousLinearMap.adjoint J) (v j))⟫_ℂ := by
    intro i j
    rw [isometryDilate_apply]
    exact (ContinuousLinearMap.adjoint_inner_left J
      ((Θ (star (a i) * a j)) ((ContinuousLinearMap.adjoint J) (v j)))
      (v i)).symm
  simp only [hterm]
  exact hΘ m a fun i ↦ (ContinuousLinearMap.adjoint J) (v i)

/-- The compression of a unital map by an isometry is unital. -/
theorem isometryCompress_one (J : K →L[ℂ] H) (Φ : B →ₗ[ℂ] (H →L[ℂ] H))
    (hJ : ∀ v : K, (ContinuousLinearMap.adjoint J) (J v) = v)
    (hone : Φ 1 = 1) : isometryCompress J Φ 1 = 1 := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [isometryCompress_apply, hone]
  exact hJ v

/-- Compression commutes with the involution. -/
theorem isometryCompress_star (J : K →L[ℂ] H) (Φ : B →ₗ[ℂ] (H →L[ℂ] H))
    (hstar : ∀ b : B, Φ (star b) = star (Φ b)) (b : B) :
    isometryCompress J Φ (star b) = star (isometryCompress J Φ b) := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hleft : ⟪isometryCompress J Φ b x, y⟫_ℂ = ⟪Φ b (J x), J y⟫_ℂ := by
    rw [isometryCompress_apply]
    exact ContinuousLinearMap.adjoint_inner_left J y ((Φ b) (J x))
  have hright : ⟪x, isometryCompress J Φ (star b) y⟫_ℂ
      = ⟪J x, Φ (star b) (J y)⟫_ℂ := by
    rw [isometryCompress_apply]
    exact ContinuousLinearMap.adjoint_inner_right J x ((Φ (star b)) (J y))
  have hmid : ⟪J x, Φ (star b) (J y)⟫_ℂ = ⟪Φ b (J x), J y⟫_ℂ := by
    rw [hstar b, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_right (Φ b) (J x) (J y)
  rw [hleft, hright, hmid]

end Transport

/-! ## Step 4, as one named statement -/

/-- **The limit step of Arveson's theorem at a `B(H)` target.**  A sequence of
form-positive maps `A → B(H)` whose matrix coefficients converge at `1` and on a
subalgebra has a form-positive limit, unital, agreeing there.

This is the Banach--Alaoglu step of the classical proof, in the only form the
compression argument needs.  It is the whole of what `arvesonBH_of_limit` below
still owes.  Note that the approximants are *not* assumed unital: the dilations
that feed it satisfy `Ψₙ(1) = Pₙ`, and unitality appears only in the limit. -/
def ArvesonLimitStatement : Prop :=
  ∀ {A : Type} [CStarAlgebra A] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : StarSubalgebra ℂ A) (Φ : ↥C →ₗ[ℂ] (H →L[ℂ] H))
    (Psi : ℕ → (A →ₗ[ℂ] (H →L[ℂ] H))),
    (∀ n, IsFormCP (Psi n)) →
      (∀ v w : H,
        Tendsto (fun n ↦ ⟪v, Psi n 1 w⟫_ℂ) atTop (𝓝 ⟪v, w⟫_ℂ)) →
        (∀ (c : ↥C) (v w : H),
          Tendsto (fun n ↦ ⟪v, Psi n (c : A) w⟫_ℂ) atTop (𝓝 ⟪v, Φ c w⟫_ℂ)) →
          ∃ Ψ : A →ₗ[ℂ] (H →L[ℂ] H), IsFormCP Ψ ∧ Ψ 1 = 1 ∧
            ∀ c : ↥C, Ψ (c : A) = Φ c

/-! ## Arveson at a `B(H)` target -/

/-- **Arveson's extension theorem at a `B(H)` target**, from the matrix case and
the limit step.  The exhausting family of isometries is data: `J n` embeds
`ℂ^{k n}` in `H`, `hJ` says each is an isometry, and the two weak-convergence
hypotheses say that `Pₙ = Jₙ Jₙ*` tends weakly to `1` and that the compressions
`Pₙ Φ(·) Pₙ` tend weakly to `Φ` on `C`. -/
theorem arvesonBH_of_limit (hlimit : ArvesonLimitStatement)
    {A : Type} [CStarAlgebra A] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : StarSubalgebra ℂ A) (hC : IsClosed (C : Set A))
    (Φ : ↥C →ₗ[ℂ] (H →L[ℂ] H))
    (hform : IsFormCP Φ) (hstar : ∀ c : ↥C, Φ (star c) = star (Φ c))
    (hone : Φ 1 = 1)
    (k : ℕ → ℕ)
    (J : ∀ n, EuclideanSpace ℂ (Fin (k n)) →L[ℂ] H)
    (hJ : ∀ (n : ℕ) (v : EuclideanSpace ℂ (Fin (k n))),
      (ContinuousLinearMap.adjoint (J n)) (J n v) = v)
    (hWOTone : ∀ v w : H,
      Tendsto (fun n ↦
        ⟪v, ((J n).comp (ContinuousLinearMap.adjoint (J n))) w⟫_ℂ)
        atTop (𝓝 ⟪v, w⟫_ℂ))
    (hWOT : ∀ (c : ↥C) (v w : H),
      Tendsto (fun n ↦
        ⟪v, (J n) ((isometryCompress (J n) Φ c)
          ((ContinuousLinearMap.adjoint (J n)) w))⟫_ℂ)
        atTop (𝓝 ⟪v, Φ c w⟫_ℂ)) :
    ∃ Ψ : A →ₗ[ℂ] (H →L[ℂ] H), IsFormCP Ψ ∧ Ψ 1 = 1 ∧
      ∀ c : ↥C, Ψ (c : A) = Φ c := by
  classical
  -- Steps 1 and 2: compress, then extend by the matrix case.
  have hstep : ∀ n : ℕ,
      ∃ Θ : A →ₗ[ℂ] (EuclideanSpace ℂ (Fin (k n)) →L[ℂ]
          EuclideanSpace ℂ (Fin (k n))),
        IsCompletelyPositive Θ ∧ Θ 1 = 1 ∧
          ∀ c : ↥C, Θ (c : A) = isometryCompress (J n) Φ c := by
    intro n
    refine exists_ucp_extension C hC (isometryCompress (J n) Φ) ?_ ?_ ?_
    · exact isFormCP_isometryCompress (J n) Φ hform
    · exact fun c ↦ isometryCompress_star (J n) Φ hstar c
    · exact isometryCompress_one (J n) Φ (hJ n) hone
  choose Θ hΘcp hΘone hΘext using hstep
  -- Step 3: dilate back to `H`, and read off the three inputs of step 4.
  refine hlimit C Φ (fun n ↦ isometryDilate (J n) (Θ n)) ?_ ?_ ?_
  · intro n
    exact isFormCP_isometryDilate (J n) (Θ n)
      (isFormCP_of_isCompletelyPositive (hΘcp n))
  · intro v w
    have hrw : ∀ n : ℕ, ∀ x : H,
        isometryDilate (J n) (Θ n) (1 : A) x
          = ((J n).comp (ContinuousLinearMap.adjoint (J n))) x := by
      intro n x
      calc isometryDilate (J n) (Θ n) (1 : A) x
          = (J n) (((Θ n) 1) ((ContinuousLinearMap.adjoint (J n)) x)) := rfl
        _ = (J n) ((1 : EuclideanSpace ℂ (Fin (k n)) →L[ℂ]
              EuclideanSpace ℂ (Fin (k n)))
                ((ContinuousLinearMap.adjoint (J n)) x)) := by rw [hΘone n]
        _ = ((J n).comp (ContinuousLinearMap.adjoint (J n))) x := rfl
    simp only [hrw]
    exact hWOTone v w
  · intro c v w
    have hrw : ∀ n : ℕ, ∀ x : H,
        isometryDilate (J n) (Θ n) (c : A) x
          = (J n) ((isometryCompress (J n) Φ c)
              ((ContinuousLinearMap.adjoint (J n)) x)) := by
      intro n x
      calc isometryDilate (J n) (Θ n) (c : A) x
          = (J n) (((Θ n) (c : A))
              ((ContinuousLinearMap.adjoint (J n)) x)) := rfl
        _ = (J n) ((isometryCompress (J n) Φ c)
              ((ContinuousLinearMap.adjoint (J n)) x)) := by rw [hΘext n c]
    simp only [hrw]
    exact hWOT c v w

end

end CStarExactness
end GroupApproximation
