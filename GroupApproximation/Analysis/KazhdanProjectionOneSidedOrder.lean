import GroupApproximation.Kazhdan.FixedSpaceCompression
import GroupApproximation.Kazhdan.KazhdanProjection
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# One-sided order for the Kazhdan projection

`non_mf_groups_exist.tex`, `lem:kazhdan-projection-order`:

> Let `L` have property (T), let `B` be a unital `C*`-algebra, and let
> `π : L → U(B)` be a homomorphism.  Denote by `P ∈ B` the image of the Kazhdan
> projection under the extension `C*_max(L) → B`.  If `U ∈ U(B)` satisfies
> `U π(L) U* ⊆ π(L)`, then `U* P U ≤ P`.

and its printed proof:

> Represent `B` faithfully and nondegenerately on a Hilbert space `H`.  The
> represented projection `P` is the orthogonal projection onto `Fix π(L)`.  If
> `ξ` is `L`-fixed and `ℓ ∈ L`, then `π(ℓ) U* ξ = U* (U π(ℓ) U*) ξ = U* ξ`,
> because `U π(ℓ) U*` belongs to `π(L)`.  Hence `U* Fix π(L) ⊆ Fix π(L)`, so
> the range projection `U* P U` is dominated by `P` in `B(H)`.

This file formalizes that proof, in the Hilbert space where the printed
argument takes place: `B = B(H)`, `U` a unitary of `B(H)` — i.e. a linear
isometry equivalence — and `P` the orthogonal projection onto the fixed
subspace of `π`.  The fixed-space description of `P` is the *hypothesis* here
rather than a consequence of a faithful nondegenerate representation of an
abstract `C*`-algebra; see *What is and is not claimed* below.

## The order relation is the genuine one

`≤` below is Mathlib's Loewner order `ContinuousLinearMap.instLoewnerPartialOrder`
on `E →L[𝕜] E`: `S ≤ T` means `T - S` is a positive operator.  No surrogate and
no absorption-identity paraphrase is used in the statement of
`conjProjection_le`, and `conjProjection_eq_star_mul` shows that the operator
being ordered is literally `star U * P * U` in the `C*`-algebra `E →L[𝕜] E`.
The absorption identities and the two scalar consequences
(`norm_conjProjection_apply_le`, `re_inner_conjProjection_le`) are recorded
afterwards for consumers that prefer an order-instance-free form.

The engine is `Submodule.starProjection_le_starProjection_iff`: for orthogonal
projections the Loewner order *is* inclusion of the subspaces projected onto.
So the whole content of the lemma is the printed one-line computation
`U* Fix π(L) ⊆ Fix π(L)`, which is `symm_mem_of_conj_mem`.

## What is and is not claimed

*Claimed.*  `U* P U ≤ P` for `P` the orthogonal projection onto the fixed
subspace of a unitary representation on a Hilbert space, `U` an arbitrary
unitary of that Hilbert space (not required to lie in the image of any ambient
group representation), under the printed inclusion `U π(Γ) U* ⊆ π(Γ)`.  This is
the form the corona argument consumes, and — via
`conjProjection_invariantProjection_le` — the ordered `P` is exactly the
operator `KazhdanProjection.invariantProjection`, i.e. the operator-norm limit
of the powers of the explicit orbit average
(`KazhdanProjection.norm_averageOperator_pow_sub_projection_le`).  So `P` here
is the Kazhdan projection, not merely *some* projection with the right range.

*Not claimed.*  The passage from an abstract unital `C*`-algebra `B` to `B(H)`.
The manuscript obtains `P` as the image of the Kazhdan projection of
`C*_max(L)` under `C*_max(L) → B` and then represents `B` faithfully and
nondegenerately.  This file takes the fixed-space description of `P` as a
hypothesis instead.  Nothing below asserts that the two agree; that bridge is
the `C*_max` obligation recorded in
`metadata/ONESIDED_TRANSPORT_FORMALIZATION_PLAN.md` §4.3.

Note also that the abstract-algebra route is already available, by a different
argument, in `Sofic/UltraproductKazhdanProjection.lean`
(`KazhdanCompressionRep.kt_09_conjugate_mul_proj`), where `P` is the spectral
projection of the orbit average at the isolated point `1` in an arbitrary
unital `C*`-algebra.  That route proves the two absorption identities without
a Hilbert space; this one proves the honest operator inequality with one.
-/

namespace GroupApproximation
namespace KazhdanProjectionOneSidedOrder

noncomputable section

/-! ## The Hilbert-space core

Everything here is about one closed subspace and one unitary; no group is
involved yet. -/

section Core

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `U* K`, the image of a subspace under the adjoint of a unitary.  For a
linear isometry equivalence the adjoint is the inverse
(`LinearIsometryEquiv.adjoint_eq_symm`), so this is `K.map U.symm`. -/
def conjSubmodule (K : Submodule 𝕜 E) (U : E ≃ₗᵢ[𝕜] E) : Submodule 𝕜 E :=
  K.map (U.symm.toLinearEquiv : E →ₗ[𝕜] E)

theorem mem_conjSubmodule {K : Submodule 𝕜 E} {U : E ≃ₗᵢ[𝕜] E} {y : E} :
    y ∈ conjSubmodule K U ↔ ∃ x ∈ K, U.symm x = y := Iff.rfl

instance conjSubmodule_hasOrthogonalProjection (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : E ≃ₗᵢ[𝕜] E) :
    (conjSubmodule K U).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.map_linearIsometryEquiv K U.symm

/-- The one-sided hypothesis, at the level of subspaces: `U* K ⊆ K`. -/
theorem conjSubmodule_le {K : Submodule 𝕜 E} {U : E ≃ₗᵢ[𝕜] E}
    (hU : ∀ x ∈ K, U.symm x ∈ K) : conjSubmodule K U ≤ K := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU x hx

/-- **`U* P U`**, the conjugate of the orthogonal projection onto `K` by a
unitary.  It is formed as the orthogonal projection onto `U* K`;
`conjProjection_apply` and `conjProjection_eq_star_mul` identify it with the
printed operator product. -/
def conjProjection (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) : E →L[𝕜] E :=
  (conjSubmodule K U).starProjection

theorem conjProjection_def (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) :
    conjProjection K U = (conjSubmodule K U).starProjection := rfl

/-- The conjugated projection acts as `x ↦ U* (P (U x))`. -/
theorem conjProjection_apply (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (x : E) :
    conjProjection K U x = U.symm (K.starProjection (U x)) :=
  Submodule.starProjection_map_apply U.symm K x

/-- The conjugated projection lands in `U* K`. -/
theorem conjProjection_apply_mem (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (x : E) : conjProjection K U x ∈ conjSubmodule K U :=
  Submodule.starProjection_apply_mem _ x

/-- **The operator being ordered is the printed one**: `U* P U`, formed in the
`C*`-algebra `E →L[𝕜] E` with its adjoint involution. -/
theorem conjProjection_eq_star_mul [CompleteSpace E] (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : E ≃ₗᵢ[𝕜] E) :
    conjProjection K U
      = star ((U : E ≃ₗᵢ[𝕜] E) : E →L[𝕜] E) * K.starProjection
          * ((U : E ≃ₗᵢ[𝕜] E) : E →L[𝕜] E) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [conjProjection_apply, LinearIsometryEquiv.star_eq_symm]
  rfl

/-- **`lem:kazhdan-projection-order`, Hilbert-space core.**  If the adjoint of
a unitary preserves a closed subspace, then the conjugated orthogonal
projection is dominated by the original one in the Loewner order.

For orthogonal projections the Loewner order is inclusion of ranges
(`Submodule.starProjection_le_starProjection_iff`), so this *is* the printed
sentence "the range projection `U* P U` is dominated by `P`". -/
theorem conjProjection_le (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[𝕜] E) (hU : ∀ x ∈ K, U.symm x ∈ K) :
    conjProjection K U ≤ K.starProjection := by
  rw [conjProjection_def]
  exact Submodule.starProjection_le_starProjection_iff.mpr (conjSubmodule_le hU)

/-- **`lem:kazhdan-projection-order`, in the printed operator product.**  The
same inequality with `U* P U` spelled out in `E →L[𝕜] E`. -/
theorem star_mul_starProjection_mul_le [CompleteSpace E] (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : E ≃ₗᵢ[𝕜] E) (hU : ∀ x ∈ K, U.symm x ∈ K) :
    star ((U : E ≃ₗᵢ[𝕜] E) : E →L[𝕜] E) * K.starProjection
        * ((U : E ≃ₗᵢ[𝕜] E) : E →L[𝕜] E)
      ≤ K.starProjection := by
  rw [← conjProjection_eq_star_mul]
  exact conjProjection_le K U hU

/-! ### Order-instance-free spellings

The two absorption identities `P Q = Q` and `Q P = Q`, which for projections
are equivalent to `Q ≤ P`, and the two scalar consequences. -/

/-- `P (U* P U) = U* P U`. -/
theorem starProjection_comp_conjProjection (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : E ≃ₗᵢ[𝕜] E) (hU : ∀ x ∈ K, U.symm x ∈ K) :
    K.starProjection ∘L conjProjection K U = conjProjection K U := by
  refine ContinuousLinearMap.ext fun x => ?_
  show K.starProjection (conjProjection K U x) = conjProjection K U x
  exact Submodule.starProjection_eq_self_iff.mpr
    (conjSubmodule_le hU (conjProjection_apply_mem K U x))

/-- `(U* P U) P = U* P U`. -/
theorem conjProjection_comp_starProjection (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : E ≃ₗᵢ[𝕜] E) (hU : ∀ x ∈ K, U.symm x ∈ K) :
    conjProjection K U ∘L K.starProjection = conjProjection K U :=
  Submodule.starProjection_comp_starProjection_of_le (conjSubmodule_le hU)

/-- `‖U* P U x‖ ≤ ‖P x‖`. -/
theorem norm_conjProjection_apply_le (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : E ≃ₗᵢ[𝕜] E) (hU : ∀ x ∈ K, U.symm x ∈ K)
    (x : E) : ‖conjProjection K U x‖ ≤ ‖K.starProjection x‖ := by
  have hstep : conjProjection K U x
      = conjProjection K U (K.starProjection x) :=
    (congrArg (fun T : E →L[𝕜] E => T x)
      (conjProjection_comp_starProjection K U hU)).symm
  rw [hstep, conjProjection_def]
  exact Submodule.norm_starProjection_apply_le _ _

/-- The quadratic-form reading of the order relation:
`re ⟪U* P U x, x⟫ ≤ re ⟪P x, x⟫`. -/
theorem re_inner_conjProjection_le (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : E ≃ₗᵢ[𝕜] E) (hU : ∀ x ∈ K, U.symm x ∈ K)
    (x : E) :
    RCLike.re (inner 𝕜 (conjProjection K U x) x)
      ≤ RCLike.re (inner 𝕜 (K.starProjection x) x) := by
  have hpos : (K.starProjection - conjProjection K U).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp (conjProjection_le K U hU)
  have hx : 0 ≤ RCLike.re
      (inner 𝕜 ((K.starProjection - conjProjection K U) x) x) :=
    hpos.re_inner_nonneg_left x
  rw [sub_apply, inner_sub_left, map_sub, sub_nonneg] at hx
  exact hx

/-- **Absorption upgrades to the order, on a Hilbert space.**  For star
projections of `E →L[𝕜] E` the algebraic identity `P Q = Q` — the
order-instance-free form in which
`Sofic/UltraproductKazhdanProjection.lean` and
`Analysis/MaximalCStarProperCompression.lean` state their conclusions, in an
arbitrary unital `C*`-algebra — is the Loewner inequality `Q ≤ P`.

So any consumer that instantiates those abstract results at `B = B(H)` gets the
printed `≤` from this lemma, with no extra analytic input. -/
theorem le_of_isStarProjection_mul_eq [CompleteSpace E] {P Q : E →L[𝕜] E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P * Q = Q) :
    Q ≤ P := by
  rw [← ContinuousLinearMap.coe_le_coe_iff]
  refine ((ContinuousLinearMap.IsStarProjection.isSymmetricProjection
    hQ).le_iff_range_le_range
      (ContinuousLinearMap.IsStarProjection.isSymmetricProjection hP)).mpr ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨Q x, congrArg (fun T : E →L[𝕜] E => T x) h⟩

end Core

/-! ## The printed hypothesis: `U π(Γ) U* ⊆ π(Γ)` -/

section Representation

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {Γ : Type*} [Group Γ]

/-- **The printed computation.**  If `U π(γ) U*` always lies in `π(Γ)`, then
`U*` preserves the fixed subspace: for `x` fixed by `π(Γ)` and `γ ∈ Γ`,

`π(γ) U* x = U* (U π(γ) U*) x = U* x`

because `U π(γ) U* = π(δ)` for some `δ`, and `x` is fixed by `π(δ)`.

The subspace `K` is *any* subspace whose members are exactly the `π(Γ)`-fixed
vectors, so the hypothesis `hK` is the sentence "`P` is the orthogonal
projection onto `Fix π(Γ)`". -/
theorem symm_mem_of_conj_mem
    (pi : Γ →* (E ≃ₗᵢ[𝕜] E)) (U : E ≃ₗᵢ[𝕜] E)
    (hconj : ∀ gamma : Γ, ∃ delta : Γ, U * pi gamma * U⁻¹ = pi delta)
    {K : Submodule 𝕜 E} (hK : ∀ x : E, x ∈ K ↔ ∀ gamma : Γ, pi gamma x = x)
    {x : E} (hx : x ∈ K) : U.symm x ∈ K := by
  rw [hK]
  intro gamma
  obtain ⟨delta, hdelta⟩ := hconj gamma
  have hfix : pi delta x = x := (hK x).mp hx delta
  have happ : U (pi gamma (U.symm x)) = x :=
    (DFunLike.congr_fun hdelta x).trans hfix
  calc
    pi gamma (U.symm x) = U.symm (U (pi gamma (U.symm x))) :=
      (U.symm_apply_apply _).symm
    _ = U.symm x := by rw [happ]

/-- **`lem:kazhdan-projection-order`, for a unitary representation.**  `U` is an
arbitrary unitary of the Hilbert space — it need not lie in the image of any
ambient group representation — and `P = K.starProjection` is the orthogonal
projection onto `Fix π(Γ)`. -/
theorem conjProjection_le_of_conj_mem
    (pi : Γ →* (E ≃ₗᵢ[𝕜] E)) (U : E ≃ₗᵢ[𝕜] E)
    (hconj : ∀ gamma : Γ, ∃ delta : Γ, U * pi gamma * U⁻¹ = pi delta)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hK : ∀ x : E, x ∈ K ↔ ∀ gamma : Γ, pi gamma x = x) :
    conjProjection K U ≤ K.starProjection :=
  conjProjection_le K U fun _ hx => symm_mem_of_conj_mem pi U hconj hK hx

/-- The same, with the compressing unitary supplied by an ambient group: this
is the shape of `Kazhdan/FixedSpaceCompression.lean`, where the printed
inclusion is `t ι(Γ) t⁻¹ ⊆ ι(Γ)` inside a group `H` acting through `ρ`. -/
theorem conjProjection_le_of_compresses
    {H : Type*} [Group H] (rho : H →* (E ≃ₗᵢ[𝕜] E)) (iota : Γ →* H) (t : H)
    (compresses : ∀ gamma : Γ, ∃ delta : Γ,
      t * iota gamma * t⁻¹ = iota delta)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hK : ∀ x : E, x ∈ K ↔ ∀ gamma : Γ, rho (iota gamma) x = x) :
    conjProjection K (rho t) ≤ K.starProjection := by
  refine conjProjection_le_of_conj_mem (rho.comp iota) (rho t) ?_ K hK
  intro gamma
  obtain ⟨delta, hdelta⟩ := compresses gamma
  refine ⟨delta, ?_⟩
  show rho t * rho (iota gamma) * (rho t)⁻¹ = rho (iota delta)
  rw [← map_inv, ← map_mul, ← map_mul, hdelta]

end Representation

/-! ## The repository's real Kazhdan projection

`HasKazhdanPropertyT` and the whole Kazhdan-pair API of this development are
stated for *real* Hilbert spaces, and `KazhdanProjection.invariantProjection`
is the operator the uniform orbit-average estimate
`KazhdanProjection.norm_averageOperator_pow_sub_projection_le` converges to.
The corollaries below put that operator on the right-hand side of the printed
inequality. -/

section RealKazhdan

variable {Γ : Type*} [Group Γ] {H : Type*} [Group H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The invariant subspace of an orthogonal representation is closed, hence
admits an orthogonal projection. -/
instance hasOrthogonalProjection_invariantSubmodule
    (rho : Γ →* (E ≃ₗᵢ[ℝ] E)) :
    (KazhdanOrthogonal.invariantSubmodule rho).HasOrthogonalProjection :=
  haveI : CompleteSpace (KazhdanOrthogonal.invariantSubmodule rho) :=
    (KazhdanProjection.isClosed_invariantSubmodule rho).completeSpace_coe
  inferInstance

/-- `KazhdanProjection.invariantProjection` is the orthogonal projection onto
the invariant subspace, on the nose. -/
theorem invariantProjection_eq_starProjection (rho : Γ →* (E ≃ₗᵢ[ℝ] E)) :
    KazhdanProjection.invariantProjection rho
      = (KazhdanOrthogonal.invariantSubmodule rho).starProjection := rfl

omit [CompleteSpace E] in
/-- `U*` preserves the invariant subspace of a one-sidedly compressed
subgroup.  This is `FixedSpaceCompression.exists_invariant_preimage`, read in
the direction the projection order needs. -/
theorem symm_mem_invariantSubmodule_of_compresses
    (rho : H →* (E ≃ₗᵢ[ℝ] E)) (iota : Γ →* H) (t : H)
    (compresses : ∀ gamma : Γ, ∃ delta : Γ,
      t * iota gamma * t⁻¹ = iota delta)
    {x : E} (hx : x ∈ KazhdanOrthogonal.invariantSubmodule (rho.comp iota)) :
    (rho t).symm x ∈ KazhdanOrthogonal.invariantSubmodule (rho.comp iota) := by
  obtain ⟨y, hy, hty⟩ :=
    FixedSpaceCompression.exists_invariant_preimage rho iota t compresses hx
  have hsymm : (rho t).symm x = y := by
    rw [← hty, LinearIsometryEquiv.symm_apply_apply]
  rw [hsymm]
  exact hy

/-- **`lem:kazhdan-projection-order` for the repository's Kazhdan projection.**
`KazhdanProjection.invariantProjection (rho.comp iota)` is the operator-norm
limit of the powers of the explicit orbit average, by
`KazhdanProjection.norm_averageOperator_pow_sub_projection_le`; the operator on
the left is its conjugate by the compressing unitary. -/
theorem conjProjection_invariantProjection_le
    (rho : H →* (E ≃ₗᵢ[ℝ] E)) (iota : Γ →* H) (t : H)
    (compresses : ∀ gamma : Γ, ∃ delta : Γ,
      t * iota gamma * t⁻¹ = iota delta) :
    conjProjection (KazhdanOrthogonal.invariantSubmodule (rho.comp iota))
        (rho t)
      ≤ KazhdanProjection.invariantProjection (rho.comp iota) := by
  rw [invariantProjection_eq_starProjection]
  exact conjProjection_le _ _ fun _ hx =>
    symm_mem_invariantSubmodule_of_compresses rho iota t compresses hx

/-- **The printed inequality `U* P U ≤ P`**, with `P` the repository's Kazhdan
projection and `U = ρ(t)` the compressing unitary, as a literal product in the
`C*`-algebra `E →L[ℝ] E`. -/
theorem star_mul_invariantProjection_mul_le
    (rho : H →* (E ≃ₗᵢ[ℝ] E)) (iota : Γ →* H) (t : H)
    (compresses : ∀ gamma : Γ, ∃ delta : Γ,
      t * iota gamma * t⁻¹ = iota delta) :
    star ((rho t : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E)
        * KazhdanProjection.invariantProjection (rho.comp iota)
        * ((rho t : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E)
      ≤ KazhdanProjection.invariantProjection (rho.comp iota) := by
  rw [invariantProjection_eq_starProjection]
  exact star_mul_starProjection_mul_le _ _ fun _ hx =>
    symm_mem_invariantSubmodule_of_compresses rho iota t compresses hx

end RealKazhdan

end

end KazhdanProjectionOneSidedOrder
end GroupApproximation
