import GroupApproximation.Analysis.VectorHilbertComplete
import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Sofic.KazhdanCornerModel

/-!
# `B_ω = ∏_ω M_{d_n}` acting on `H_ω`

`\label{thm:normal-kazhdan}` opens its Kazhdan-corner paragraph with

> Fix a free ultrafilter `ω`, let `H_ω` be the Hilbert-space ultraproduct of the
> coordinate spaces `ℂ^{d_n}`, and let `B_ω = ∏_ω B(ℂ^{d_n})` act on it as in
> Section~\ref{sec:transport}, so that the classes `π(g) = [V_{g,n}]_ω` define a
> unitary representation of `H̄` on `H_ω`.

`Analysis/VectorHilbertUltraproduct.lean` built `H_ω` and gave it its inner
product; `Analysis/VectorHilbertComplete.lean` made it complete, hence a Hilbert
space in mathlib's sense.  What both files' closing sections name as the next
step, and what nothing in the development supplied, is the sentence's second
clause: the **action**.  This file is that clause.

## What is here

`B_ω` is not a new object.  `Analysis/NormMatrixCorona.lean` already builds the
bounded sequences `lp (fun n ↦ M_{d_n}(ℂ)) ∞` and, for any filter, the ideal of
sequences whose coordinate operator norms vanish along it; at a free ultrafilter
that quotient is the printed `∏_ω M_{d_n}`.  What is new is that it acts:

* `actFam` — the coordinatewise action `(A · ξ)_n = A_n ξ_n`, on raw families;
* `vecMass_mulVec_le` — the estimate that makes everything else work,
  `mass (A_n ξ_n) ≤ ‖A_n‖² · mass (ξ_n)`, which is
  `KazhdanCornerMatrices.sum_normSq_mulVec_le_general` read through `vecMass`;
* `actFam_mem_vecBounded` — hence the action preserves `vecBounded`, and
  `actSub` is it as a `ℂ`-linear map there;
* `actFam_mem_vecNull` and `actFam_mem_vecNull_of_null` — the two null
  directions, one for each argument: a null vector family stays null under a
  bounded matrix family, and a *null matrix family* sends a bounded vector
  family to a null one.  The second is why the action descends to the quotient
  in the algebra variable as well as the vector variable, which is what makes it
  an action of `B_ω` rather than of the bounded sequences;
* `actQ` — the resulting `ℂ`-linear endomorphism of `H_ω`, with `actQ_mkV` its
  defining equation on classes;
* `norm_actQ_le` — it is bounded, by the corona norm;
* `actQ_mul`, `actQ_one`, `actQ_add`, `actQ_eq_zero_of_null` — multiplicativity,
  unitality, additivity, and the vanishing on null classes;
* `norm_actQ_of_unitary` and `actIsometryEquiv` — for a coordinatewise
  **unitary** family the action is norm preserving on the nose, not merely
  bounded, and with an inverting class it is a `LinearIsometryEquiv`.  This is
  the form the printed `π(g)` has, and the form a unitary representation has to
  land in;
* `OmegaUnitaryRep` and `rep'` — the manuscript's hypothesis, the coordinate
  family only `ω`-multiplicative, and the representation it defines.

## Why norm preservation is exact, and boundedness only an estimate

For a general class of `B_ω` the operator norm on `H_ω` is bounded by the corona
norm and no better: the corona norm is an ultralimit of coordinate norms and the
action's norm is a supremum over unit vectors of `H_ω`, and the two need not
agree.  For the classes the manuscript actually forms there is nothing to
estimate.  `π(g)` has the coordinatewise unitary representative `V_{g,n}`, and
unitary matrices preserve `∑ᵢ |xᵢ|²` exactly
(`KazhdanCornerMatrices.sum_normSq_mulVec_of_star_mul_self`), so the coordinate
masses are *equal* and the ultralimit of equals is an equality.  This is the same
distinction `Analysis/OmegaIsometryRepresentation.lean` draws for `K_ω`, and for
the same reason.

## Scope

The vector spaces here carry no weight.  `K_ω` of `Sofic/KOmegaHilbert.lean` is
the ultraproduct of the *matrix* spaces `M_{d_n}(ℂ)` under a renormalized
Hilbert--Schmidt inner product and its ambient algebra is the corona on the
doubled index `Y n × Y n`, because `B(K_n)` is `M_{d_n²}`.  The renormalization
in `thm:normal-kazhdan` is of the *trace* on the corner, not of the coordinate
Hilbert spaces, so `H_ω` needs none and its ambient is the corona on the
undoubled index.  Nothing below is a specialization of the `K_ω` chain and
nothing in the `K_ω` chain specializes to it.
-/

namespace GroupApproximation
namespace VectorOmegaAction

open Filter Matrix Topology
open KazhdanCornerMatrices MarkedCompressionVectorChain UltrafilterLimit
open VectorHilbertUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : ℕ → FiniteModel}

/-! ## The coordinate estimate -/

section Coordinates

variable {Z : FiniteModel}

/-- **The estimate the whole file rests on.**  A matrix moves the coordinate
mass by at most the square of its operator norm.  This is
`sum_normSq_mulVec_le_general` with `vecMass` unfolded on both sides. -/
theorem vecMass_mulVec_le (A : Matrix Z Z ℂ) (x : Z → ℂ) :
    vecMass (A *ᵥ x) ≤ ‖A‖ ^ 2 * vecMass x :=
  sum_normSq_mulVec_le_general A x

/-- A coordinatewise unitary preserves the coordinate mass **exactly**. -/
theorem vecMass_mulVec_of_unitary {U : Matrix Z Z ℂ} (hU : Uᴴ * U = 1)
    (x : Z → ℂ) : vecMass (U *ᵥ x) = vecMass x :=
  sum_normSq_mulVec_of_star_mul_self hU x

end Coordinates

/-! ## The action on raw families -/

section Families

/-- The coordinatewise action of a matrix family on a vector family. -/
def actFam (A : ∀ n, Matrix (Y n) (Y n) ℂ) (ξ : VecFam Y) : VecFam Y :=
  fun n ↦ A n *ᵥ ξ n

@[simp] theorem actFam_apply (A : ∀ n, Matrix (Y n) (Y n) ℂ) (ξ : VecFam Y)
    (n : ℕ) : actFam A ξ n = A n *ᵥ ξ n := rfl

theorem actFam_add (A : ∀ n, Matrix (Y n) (Y n) ℂ) (ξ η : VecFam Y) :
    actFam A (ξ + η) = actFam A ξ + actFam A η := by
  funext n
  exact Matrix.mulVec_add _ _ _

theorem actFam_smul (A : ∀ n, Matrix (Y n) (Y n) ℂ) (c : ℂ) (ξ : VecFam Y) :
    actFam A (c • ξ) = c • actFam A ξ := by
  funext n
  exact Matrix.mulVec_smul (A n) c (ξ n)

theorem actFam_zero (A : ∀ n, Matrix (Y n) (Y n) ℂ) :
    actFam A (0 : VecFam Y) = 0 := by
  funext n
  exact Matrix.mulVec_zero _

theorem actFam_one (ξ : VecFam Y) :
    actFam (fun n ↦ (1 : Matrix (Y n) (Y n) ℂ)) ξ = ξ := by
  funext n
  exact Matrix.one_mulVec _

theorem actFam_mul (A B : ∀ n, Matrix (Y n) (Y n) ℂ) (ξ : VecFam Y) :
    actFam (fun n ↦ A n * B n) ξ = actFam A (actFam B ξ) := by
  funext n
  exact (Matrix.mulVec_mulVec (ξ n) (A n) (B n)).symm

theorem actFam_add_left (A B : ∀ n, Matrix (Y n) (Y n) ℂ) (ξ : VecFam Y) :
    actFam (fun n ↦ A n + B n) ξ = actFam A ξ + actFam B ξ := by
  funext n
  exact Matrix.add_mulVec (A n) (B n) (ξ n)

end Families

/-! ## The ambient algebra

`B_ω = ∏_ω M_{d_n}` is the corona of `Analysis/NormMatrixCorona.lean` at the
ultrafilter, on the **undoubled** index.  `DblIdx` is the doubled one, which is
what `K_ω` needs and this space does not. -/

section Ambient

/-- The coordinate index, as a family of bare types.  Mirrors `DblIdx`, without
the doubling: the operators here act on `ℂ^{d_n}` itself. -/
abbrev Idx (Y : ℕ → FiniteModel) : ℕ → Type := fun n ↦ ((Y n : FiniteModel) : Type)

variable (Y) [∀ n, Nonempty (Y n)]

instance instNonemptyIdx (n : ℕ) : Nonempty (Idx Y n) := by
  show Nonempty (Y n)
  infer_instance

/-- **The printed `B_ω = ∏_ω B(ℂ^{d_n})`**, as the filter corona at `ω`. -/
abbrev BOmega (ω : Ultrafilter ℕ) : Type :=
  FilterMatrixCoronaAlgebra (Idx Y) (ω : Filter ℕ)

end Ambient

/-! ## The action preserves the numerator and the denominator -/

section Descent

variable (Y) (ω : Ultrafilter ℕ)

theorem actFam_mem_vecBounded (a : ∀ n, Matrix (Y n) (Y n) ℂ) {C : ℝ}
    (hC : ∀ n, ‖a n‖ ≤ C) {ξ : VecFam Y} (hξ : ξ ∈ vecBounded Y) :
    actFam a ξ ∈ vecBounded Y := by
  obtain ⟨M, hM⟩ := hξ
  refine ⟨C ^ 2 * M, fun n ↦ ?_⟩
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (a n)) (hC n)
  calc vecMass (actFam a ξ n)
      ≤ ‖a n‖ ^ 2 * vecMass (ξ n) := vecMass_mulVec_le (a n) (ξ n)
    _ ≤ C ^ 2 * M := by
        refine mul_le_mul (by nlinarith [norm_nonneg (a n), hC n]) (hM n)
          (vecMass_nonneg _) (by positivity)

/-- **A null vector family stays null.**  The bound is uniform in `n`, so the
`ε` is simply divided by it. -/
theorem actFam_mem_vecNull (a : ∀ n, Matrix (Y n) (Y n) ℂ) {C : ℝ}
    (hC : ∀ n, ‖a n‖ ≤ C) {ξ : VecFam Y} (hξ : ξ ∈ vecNull Y ω) :
    actFam a ξ ∈ vecNull Y ω := by
  intro ε hε
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (a 0)) (hC 0)
  have hden : (0 : ℝ) < C ^ 2 + 1 := by positivity
  filter_upwards [hξ (ε / (C ^ 2 + 1)) (div_pos hε hden)] with n hn
  show vecMass (actFam a ξ n) ≤ ε
  have hsq : ‖a n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (a n), hC n]
  calc vecMass (actFam a ξ n)
      ≤ ‖a n‖ ^ 2 * vecMass (ξ n) := vecMass_mulVec_le (a n) (ξ n)
    _ ≤ C ^ 2 * (ε / (C ^ 2 + 1)) :=
        mul_le_mul hsq hn (vecMass_nonneg _) (by positivity)
    _ = (C ^ 2 / (C ^ 2 + 1)) * ε := by ring
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right ((div_le_one hden).2 (by linarith)) hε.le
    _ = ε := one_mul ε

/-- **A null *matrix* family sends a bounded vector family to a null one.**
This is the direction that makes the action descend in the algebra variable,
so that `B_ω` acts and not merely the bounded sequences. -/
theorem actFam_mem_vecNull_of_null {a : ∀ n, Matrix (Y n) (Y n) ℂ}
    (ha : Tendsto (fun n ↦ ‖a n‖) (ω : Filter ℕ) (nhds 0))
    {ξ : VecFam Y} (hξ : ξ ∈ vecBounded Y) :
    actFam a ξ ∈ vecNull Y ω := by
  obtain ⟨M, hM⟩ := hξ
  have hM0 : 0 ≤ M := le_trans (vecMass_nonneg (ξ 0)) (hM 0)
  intro ε hε
  have hden : (0 : ℝ) < M + 1 := by linarith
  have hpos : 0 < Real.sqrt (ε / (M + 1)) := Real.sqrt_pos.2 (div_pos hε hden)
  have hev : ∀ᶠ n in (ω : Filter ℕ), ‖a n‖ < Real.sqrt (ε / (M + 1)) := by
    have := ha (Metric.ball_mem_nhds (0 : ℝ) hpos)
    filter_upwards [this] with n hn
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (a n))] using hn
  filter_upwards [hev] with n hn
  show vecMass (actFam a ξ n) ≤ ε
  have hsq : ‖a n‖ ^ 2 ≤ ε / (M + 1) := by
    have h1 : ‖a n‖ ^ 2 ≤ Real.sqrt (ε / (M + 1)) ^ 2 := by
      nlinarith [norm_nonneg (a n), hn]
    rwa [Real.sq_sqrt (le_of_lt (div_pos hε hden))] at h1
  calc vecMass (actFam a ξ n)
      ≤ ‖a n‖ ^ 2 * vecMass (ξ n) := vecMass_mulVec_le (a n) (ξ n)
    _ ≤ (ε / (M + 1)) * M :=
        mul_le_mul hsq (hM n) (vecMass_nonneg _) (by positivity)
    _ = (M / (M + 1)) * ε := by ring
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right ((div_le_one hden).2 (by linarith)) hε.le
    _ = ε := one_mul ε

end Descent

/-! ## The action as an endomorphism of `H_ω` -/

section Endomorphism

-- No `Nonempty` here: `BoundedMatrixSequence` is `lp` over the matrix algebras
-- and needs none, and neither does anything below.  `BOmega` above does, which
-- is why the instance is stated there rather than in this section.
variable (Y) (ω : Ultrafilter ℕ)

/-- The action on the numerator. -/
def actSub (a : BoundedMatrixSequence (Idx Y)) :
    vecBounded Y →ₗ[ℂ] vecBounded Y where
  toFun ξ := ⟨actFam (fun n ↦ a n) (ξ : VecFam Y),
    actFam_mem_vecBounded Y (fun n ↦ a n)
      (boundedMatrixSequence_coord_norm_le (Idx Y) a) ξ.2⟩
  map_add' ξ η := Subtype.ext (actFam_add (fun n ↦ a n) (ξ : VecFam Y) (η : VecFam Y))
  map_smul' c ξ := Subtype.ext (actFam_smul (fun n ↦ a n) c (ξ : VecFam Y))

@[simp] theorem actSub_coe (a : BoundedMatrixSequence (Idx Y))
    (ξ : vecBounded Y) :
    ((actSub Y a ξ : vecBounded Y) : VecFam Y) = actFam (fun n ↦ a n) (ξ : VecFam Y) :=
  rfl

theorem vecNullIn_le_comap (a : BoundedMatrixSequence (Idx Y)) :
    vecNullIn Y ω ≤ Submodule.comap (actSub Y a) (vecNullIn Y ω) := fun _ξ hξ ↦
  actFam_mem_vecNull Y ω (fun n ↦ a n)
    (boundedMatrixSequence_coord_norm_le (Idx Y) a) hξ

/-- **The action of an operator sequence on `H_ω`.** -/
def actQ (a : BoundedMatrixSequence (Idx Y)) :
    VecOmega Y ω →ₗ[ℂ] VecOmega Y ω :=
  Submodule.mapQ (vecNullIn Y ω) (vecNullIn Y ω) (actSub Y a)
    (vecNullIn_le_comap Y ω a)

@[simp] theorem actQ_mkV (a : BoundedMatrixSequence (Idx Y)) (ξ : vecBounded Y) :
    actQ Y ω a (mkV Y ω ξ) = mkV Y ω (actSub Y a ξ) :=
  Submodule.mapQ_apply _ _ _ ξ

/-- Two endomorphisms of `H_ω` agree once they agree on classes. -/
theorem vecOmega_linearMap_ext {f g : VecOmega Y ω →ₗ[ℂ] VecOmega Y ω}
    (h : ∀ ξ : vecBounded Y, f (mkV Y ω ξ) = g (mkV Y ω ξ)) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨ξ, rfl⟩ := mkV_surjective Y ω x
  exact h ξ

/-- The algebra structure on `lp … ∞` -- and so the `1` and the product the two
statements below are about -- is where `Nonempty` is genuinely needed; nothing
above it is. -/
theorem actQ_one [∀ n, Nonempty (Y n)] : actQ Y ω 1 = LinearMap.id := by
  refine vecOmega_linearMap_ext Y ω fun ξ ↦ ?_
  rw [actQ_mkV]
  exact congrArg (mkV Y ω) (Subtype.ext (actFam_one (ξ : VecFam Y)))

-- No `Nonempty` needed here, unlike `actQ_one`: the multiplication on
-- `lp … ∞` is coordinatewise and asks nothing of the index, while the `1` does.
theorem actQ_mul (a b : BoundedMatrixSequence (Idx Y)) :
    actQ Y ω (a * b) = (actQ Y ω a).comp (actQ Y ω b) := by
  refine vecOmega_linearMap_ext Y ω fun ξ ↦ ?_
  rw [actQ_mkV]
  show mkV Y ω (actSub Y (a * b) ξ) = actQ Y ω a (actQ Y ω b (mkV Y ω ξ))
  rw [actQ_mkV, actQ_mkV]
  exact congrArg (mkV Y ω)
    (Subtype.ext (actFam_mul (fun n ↦ a n) (fun n ↦ b n) (ξ : VecFam Y)))

end Endomorphism

/-! ## The action is bounded by the corona norm

The docstring at the head of this file lists `norm_actOmega_le`; this is it.
For a general class only the estimate is available, not the equality the unitary
case gets. -/

section Bounded

variable (Y) (ω : Ultrafilter ℕ)

/-- Ultralimits are monotone.  Not in `Sofic/UltrafilterLimit.lean`, which has
the two one-sided bounds against a constant but not the comparison of two
limits; it follows from those by subtracting. -/
theorem ulim_mono {f g : ℕ → ℝ}
    (hf : ∃ L : ℝ, Filter.Tendsto f (ω : Filter ℕ) (nhds L))
    (hg : ∃ L : ℝ, Filter.Tendsto g (ω : Filter ℕ) (nhds L))
    (h : ∀ n, f n ≤ g n) : UltrafilterLimit.ulim ω f ≤ UltrafilterLimit.ulim ω g := by
  have hsub : UltrafilterLimit.ulim ω (fun n ↦ g n - f n)
      = UltrafilterLimit.ulim ω g - UltrafilterLimit.ulim ω f :=
    UltrafilterLimit.ulim_sub hg hf
  have hnn : 0 ≤ UltrafilterLimit.ulim ω (fun n ↦ g n - f n) := by
    refine UltrafilterLimit.ulim_nonneg ?_ fun n ↦ sub_nonneg.2 (h n)
    obtain ⟨Lg, hLg⟩ := hg
    obtain ⟨Lf, hLf⟩ := hf
    exact ⟨Lg - Lf, hLg.sub hLf⟩
  linarith [hsub ▸ hnn]

/-- A constant passes through an ultralimit. -/
theorem ulim_const_smul (c : ℝ) {f : ℕ → ℝ}
    (hf : ∃ L : ℝ, Filter.Tendsto f (ω : Filter ℕ) (nhds L)) :
    UltrafilterLimit.ulim ω (fun n ↦ c * f n) = c * UltrafilterLimit.ulim ω f := by
  obtain ⟨L, hL⟩ := hf
  have hlim : UltrafilterLimit.ulim ω f = L := UltrafilterLimit.ulim_eq hL
  refine UltrafilterLimit.ulim_eq ?_
  rw [hlim]
  exact hL.const_mul c

/-- **The action is bounded by the corona norm.**  For a general class this is
an estimate and not an equality; the unitary case below is exact. -/
theorem norm_actQ_le (a : BoundedMatrixSequence (Idx Y)) (x : VecOmega Y ω) :
    ‖actQ Y ω a x‖ ≤ ‖a‖ * ‖x‖ := by
  obtain ⟨ξ, rfl⟩ := mkV_surjective Y ω x
  rw [actQ_mkV, norm_mkV, norm_mkV]
  have hbnd : ∀ n, ‖(a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n‖ ≤ ‖a‖ :=
    boundedMatrixSequence_coord_norm_le (Idx Y) a
  have hA : ∀ n, vecMass (((actSub Y a ξ : vecBounded Y) : VecFam Y) n)
      ≤ ‖a‖ ^ 2 * vecMass ((ξ : VecFam Y) n) := by
    intro n
    have h1 := vecMass_mulVec_le ((a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)
      ((ξ : VecFam Y) n)
    refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ (vecMass_nonneg _))
    have h0 : (0 : ℝ) ≤ ‖(a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n‖ := norm_nonneg _
    nlinarith [hbnd n]
  have hex1 := exists_tendsto_vecMass (Y := Y) (ω := ω) (actSub Y a ξ)
  have hex2 := exists_tendsto_vecMass (Y := Y) (ω := ω) ξ
  have hexs : ∃ L : ℝ, Filter.Tendsto
      (fun n ↦ ‖a‖ ^ 2 * vecMass ((ξ : VecFam Y) n)) (ω : Filter ℕ) (nhds L) := by
    obtain ⟨L, hL⟩ := hex2
    exact ⟨‖a‖ ^ 2 * L, hL.const_mul _⟩
  have hmono := ulim_mono ω hex1 hexs hA
  rw [ulim_const_smul ω (‖a‖ ^ 2) hex2] at hmono
  have hnn2 : 0 ≤ UltrafilterLimit.ulim ω
      (fun n ↦ vecMass ((ξ : VecFam Y) n)) :=
    UltrafilterLimit.ulim_nonneg hex2 fun n ↦ vecMass_nonneg _
  calc Real.sqrt (UltrafilterLimit.ulim ω
        (fun n ↦ vecMass (((actSub Y a ξ : vecBounded Y) : VecFam Y) n)))
      ≤ Real.sqrt (‖a‖ ^ 2 * UltrafilterLimit.ulim ω
          (fun n ↦ vecMass ((ξ : VecFam Y) n))) := Real.sqrt_le_sqrt hmono
    _ = ‖a‖ * Real.sqrt (UltrafilterLimit.ulim ω
          (fun n ↦ vecMass ((ξ : VecFam Y) n))) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg a)]

end Bounded

/-! ## Linearity in the algebra variable, and the bounded operator

With `norm_actQ_le` the action of each class is a bounded operator, and with
`actQ_smul` the assignment is `ℂ`-linear, so what is left before a
⋆-homomorphism is the adjoint below. -/

section Smul

variable (Y) (ω : Ultrafilter ℕ)

theorem actFam_smul_left (c : ℂ) (A : ∀ n, Matrix (Y n) (Y n) ℂ) (ξ : VecFam Y) :
    actFam (fun n ↦ c • A n) ξ = c • actFam A ξ := by
  funext n
  exact Matrix.smul_mulVec c (A n) (ξ n)

theorem actQ_smul (c : ℂ) (a : BoundedMatrixSequence (Idx Y)) :
    actQ Y ω (c • a) = c • actQ Y ω a := by
  refine vecOmega_linearMap_ext Y ω fun ξ ↦ ?_
  rw [actQ_mkV]
  show mkV Y ω (actSub Y (c • a) ξ) = c • actQ Y ω a (mkV Y ω ξ)
  rw [actQ_mkV]
  have hsm : actSub Y (c • a) ξ = c • actSub Y a ξ :=
    Subtype.ext (actFam_smul_left Y c (fun n ↦ a n) (ξ : VecFam Y))
  rw [hsm]
  exact (Submodule.Quotient.mk_smul _ _ _)

/-- **The action of a class, as a bounded operator on `H_ω`.** -/
def actCLM (a : BoundedMatrixSequence (Idx Y)) :
    VecOmega Y ω →L[ℂ] VecOmega Y ω :=
  LinearMap.mkContinuous (actQ Y ω a) ‖a‖ (norm_actQ_le Y ω a)

@[simp] theorem actCLM_apply (a : BoundedMatrixSequence (Idx Y))
    (x : VecOmega Y ω) : actCLM Y ω a x = actQ Y ω a x := rfl

end Smul

/-! ## The adjoint

`⟪a·ξ, η⟫ = ⟪ξ, a*·η⟫`, first at a coordinate and then in `H_ω`.  This is what
makes the action a ⋆-map, and with `norm_actQ_le` it is everything a
⋆-homomorphism into `B(H_ω)` needs beyond what is already above. -/

section Adjoint

variable {Z : FiniteModel}

/-- The coordinate adjoint identity, by exchanging the order of summation.
`(Aᴴ y)_j = ∑ᵢ conj(A i j) yᵢ` is what makes the two double sums the same. -/
theorem inner_evec_mulVec (A : Matrix Z Z ℂ) (x y : Z → ℂ) :
    (inner ℂ (evec (A *ᵥ x)) (evec y) : ℂ)
      = inner ℂ (evec x) (evec (Aᴴ *ᵥ y)) := by
  classical
  rw [inner_evec, inner_evec]
  have hl : ∀ i : Z, (starRingEnd ℂ) ((A *ᵥ x) i) * y i
      = ∑ j : Z, (starRingEnd ℂ) (A i j) * (starRingEnd ℂ) (x j) * y i := by
    intro i
    show (starRingEnd ℂ) (∑ j : Z, A i j * x j) * y i = _
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_mul]
  have hr : ∀ j : Z, (starRingEnd ℂ) (x j) * (Aᴴ *ᵥ y) j
      = ∑ i : Z, (starRingEnd ℂ) (A i j) * (starRingEnd ℂ) (x j) * y i := by
    intro j
    show (starRingEnd ℂ) (x j) * (∑ i : Z, Aᴴ j i * y i) = _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    show (starRingEnd ℂ) (x j) * ((starRingEnd ℂ) (A i j) * y i) = _
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hl i, Finset.sum_congr rfl fun j _ ↦ hr j,
    Finset.sum_comm]

end Adjoint

section AdjointOmega

variable (Y) (ω : Ultrafilter ℕ)

@[simp] theorem star_coord (a : BoundedMatrixSequence (Idx Y)) (n : ℕ) :
    ((star a : BoundedMatrixSequence (Idx Y)) :
        ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
      = ((a : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)ᴴ := rfl

/-- **The adjoint identity in `H_ω`.**  Both sides are the ultralimit of the
same coordinate pairing, so the identity is the coordinate one taken along `ω`
and nothing else. -/
theorem inner_actQ (a : BoundedMatrixSequence (Idx Y)) (x y : VecOmega Y ω) :
    (inner ℂ (actQ Y ω a x) y : ℂ) = inner ℂ x (actQ Y ω (star a) y) := by
  obtain ⟨ξ, rfl⟩ := mkV_surjective Y ω x
  obtain ⟨η, rfl⟩ := mkV_surjective Y ω y
  show uvinner (ω := ω) (actSub Y a ξ) η
      = uvinner (ω := ω) ξ (actSub Y (star a) η)
  refine congrArg (UltrafilterLimit.ulim ω) (funext fun n ↦ ?_)
  show (inner ℂ (evec (((actSub Y a ξ : vecBounded Y) : VecFam Y) n))
        (evec ((η : VecFam Y) n)) : ℂ)
    = inner ℂ (evec ((ξ : VecFam Y) n))
        (evec (((actSub Y (star a) η : vecBounded Y) : VecFam Y) n))
  exact inner_evec_mulVec _ _ _

end AdjointOmega

/-! ## Coordinatewise unitaries act by isometries

This is the half of the printed sentence that says *unitary* representation.
For a general class of `B_ω` only the corona-norm estimate is available; here
the coordinate masses are equal on the nose, so the ultralimits are equal and
the norm is preserved exactly. -/

section Unitary

variable (Y) (ω : Ultrafilter ℕ)

/-- **A coordinatewise unitary class acts by a norm-preserving map.** -/
theorem norm_actQ_of_unitary {a : BoundedMatrixSequence (Idx Y)}
    (ha : ∀ n, (a n)ᴴ * (a n) = 1) (x : VecOmega Y ω) :
    ‖actQ Y ω a x‖ = ‖x‖ := by
  obtain ⟨ξ, rfl⟩ := mkV_surjective Y ω x
  rw [actQ_mkV, norm_mkV, norm_mkV]
  have hfun : (fun n ↦ vecMass (((actSub Y a ξ : vecBounded Y) : VecFam Y) n))
      = fun n ↦ vecMass ((ξ : VecFam Y) n) := by
    funext n
    exact vecMass_mulVec_of_unitary (ha n) ((ξ : VecFam Y) n)
  rw [hfun]

variable [∀ n, Nonempty (Y n)]

/-- **`π(g)` as the printed sentence needs it.**  A coordinatewise unitary
class, together with the class inverting it in `B_ω`, acts on `H_ω` as a
surjective linear isometry -- which is what "unitary representation" means for
a Hilbert space in mathlib.

The inverse class is taken as data rather than manufactured from `a`, because
that is how the representation supplies it: the manuscript's `π(g)` has
`π(g⁻¹)` for an inverse, and the group hands both over at once. -/
def actIsometryEquiv (a b : BoundedMatrixSequence (Idx Y))
    (hab : a * b = 1) (hba : b * a = 1)
    (ha : ∀ n, (a n)ᴴ * (a n) = 1) :
    VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω where
  toLinearEquiv :=
    LinearEquiv.ofLinear (actQ Y ω a) (actQ Y ω b)
      (by rw [← actQ_mul, hab, actQ_one]) (by rw [← actQ_mul, hba, actQ_one])
  norm_map' := norm_actQ_of_unitary Y ω ha

@[simp] theorem actIsometryEquiv_apply (a b : BoundedMatrixSequence (Idx Y))
    (hab : a * b = 1) (hba : b * a = 1) (ha : ∀ n, (a n)ᴴ * (a n) = 1)
    (x : VecOmega Y ω) :
    actIsometryEquiv Y ω a b hab hba ha x = actQ Y ω a x := rfl

end Unitary

/-! ## Additivity in the algebra variable, and the null class

An operator sequence that is null along `ω` acts as zero, so two sequences whose
difference is null act identically.  This is what makes the manuscript's
*asymptotically* multiplicative `V_{g,n}` give an *exactly* multiplicative
`π`: the defect is null along `ω`, so it disappears in the action. -/

section Algebra

variable (Y) (ω : Ultrafilter ℕ)

theorem actQ_add (a b : BoundedMatrixSequence (Idx Y)) :
    actQ Y ω (a + b) = actQ Y ω a + actQ Y ω b := by
  refine vecOmega_linearMap_ext Y ω fun ξ ↦ ?_
  rw [actQ_mkV]
  show mkV Y ω (actSub Y (a + b) ξ) = actQ Y ω a (mkV Y ω ξ) + actQ Y ω b (mkV Y ω ξ)
  rw [actQ_mkV, actQ_mkV]
  have hsum : actSub Y (a + b) ξ = actSub Y a ξ + actSub Y b ξ :=
    Subtype.ext (actFam_add_left (fun n ↦ a n) (fun n ↦ b n) (ξ : VecFam Y))
  rw [hsum]
  rfl

/-- **A null class acts as zero.**  This is the descent in the algebra
variable: it is what says the action is an action of `B_ω`, the quotient, and
not merely of the bounded sequences. -/
theorem actQ_eq_zero_of_null {a : BoundedMatrixSequence (Idx Y)}
    (ha : IsNullMatrixSequence (Idx Y) (ω : Filter ℕ) a) : actQ Y ω a = 0 := by
  refine vecOmega_linearMap_ext Y ω fun ξ ↦ ?_
  rw [actQ_mkV]
  show mkV Y ω (actSub Y a ξ) = (0 : VecOmega Y ω)
  rw [show (0 : VecOmega Y ω) = mkV Y ω 0 from rfl]
  refine (Submodule.Quotient.eq (vecNullIn Y ω)).2 ?_
  have hmem : actFam (fun n ↦ a n) (ξ : VecFam Y) ∈ vecNull Y ω :=
    actFam_mem_vecNull_of_null Y ω ha ξ.2
  -- `vecNullIn` is `vecNull` pulled back along the inclusion of `vecBounded`,
  -- so membership there is membership of the underlying family.
  rw [sub_zero]
  exact hmem

/-- **Two sequences with null difference act identically.** -/
theorem actQ_eq_of_sub_null {a b : BoundedMatrixSequence (Idx Y)}
    (h : IsNullMatrixSequence (Idx Y) (ω : Filter ℕ) (a - b)) :
    actQ Y ω a = actQ Y ω b := by
  have hz : actQ Y ω (a - b) = 0 := actQ_eq_zero_of_null Y ω h
  have hsub : actQ Y ω (a - b) + actQ Y ω b = actQ Y ω a := by
    rw [← actQ_add]
    congr 1
    abel
  rw [hz] at hsub
  simpa using hsub.symm

end Algebra

/-! ## The action as a continuous unital ⋆-homomorphism

Everything above assembles: `actQ` is linear in the vector, linear and
multiplicative and unital in the algebra variable, bounded by the corona norm,
and carries `star` to the adjoint.  That is exactly a unital ⋆-homomorphism of
complex algebras `∏_n B(ℂ^{d_n}) → B(H_ω)`, and it kills the `ω`-null sequences
(`actQ_eq_zero_of_null`), so it is the action of `B_ω` written on
representatives. -/

section StarHom

variable (Y) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)]

omit [∀ n, Nonempty (Y n)] in
theorem actQ_zero : actQ Y ω 0 = 0 := by
  refine vecOmega_linearMap_ext Y ω fun ξ ↦ ?_
  rw [actQ_mkV]
  show mkV Y ω (actSub Y 0 ξ) = (0 : VecOmega Y ω →ₗ[ℂ] VecOmega Y ω) (mkV Y ω ξ)
  have h0 : actSub Y (0 : BoundedMatrixSequence (Idx Y)) ξ = 0 :=
    Subtype.ext (by
      funext n
      exact Matrix.zero_mulVec ((ξ : VecFam Y) n))
  rw [h0]
  simp

omit [∀ n, Nonempty (Y n)] in
/-- **`star` goes to the adjoint.** -/
theorem actCLM_star (a : BoundedMatrixSequence (Idx Y)) :
    actCLM Y ω (star a) = ContinuousLinearMap.adjoint (actCLM Y ω a) := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y ↦ ?_
  have h := inner_actQ Y ω (star a) x y
  rwa [star_star] at h

/-- **The action of `∏_n B(ℂ^{d_n})` on `H_ω`, as a unital ⋆-homomorphism.**

This is the object `NK.06`'s remaining clause needs: with it, the range is a
unital ⋆-subalgebra of `B(H_ω)` containing the average `h`, and the question
whether the spectral projection of `h` lies in the norm ultraproduct becomes the
question whether that range is closed. -/
def actStarAlgHom :
    BoundedMatrixSequence (Idx Y) →⋆ₐ[ℂ] (VecOmega Y ω →L[ℂ] VecOmega Y ω) where
  toFun := actCLM Y ω
  map_one' := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    show actQ Y ω 1 x = x
    rw [actQ_one]
    rfl
  map_mul' a b := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    show actQ Y ω (a * b) x = actQ Y ω a (actQ Y ω b x)
    rw [actQ_mul]
    rfl
  map_zero' := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    show actQ Y ω 0 x = 0
    rw [actQ_zero]
    rfl
  map_add' a b := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    show actQ Y ω (a + b) x = actQ Y ω a x + actQ Y ω b x
    rw [actQ_add]
    rfl
  commutes' r := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    show actQ Y ω (algebraMap ℂ (BoundedMatrixSequence (Idx Y)) r) x
      = (algebraMap ℂ (VecOmega Y ω →L[ℂ] VecOmega Y ω) r) x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      actQ_smul, actQ_one]
    rfl
  map_star' a := actCLM_star Y ω a

@[simp] theorem actStarAlgHom_apply (a : BoundedMatrixSequence (Idx Y)) :
    actStarAlgHom Y ω a = actCLM Y ω a := rfl

end StarHom

/-! ## `π(g) = [V_{g,n}]_ω`

The printed sentence, for a family of coordinate unitaries.  Two forms: a
strictly multiplicative family gives a unitary representation outright, and an
*asymptotically* multiplicative one -- which is what an operator-norm asymptotic
representation supplies, and what `thm:normal-kazhdan` actually has -- gives the
same thing, because the defect is null along `ω` and a null class acts as
zero. -/

section Representation

variable (Y) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)]
variable {H : Type*} [Group H]

/-- A family of coordinate unitaries, as a bounded sequence.  Bounded by `1`,
because a unitary of a C*-algebra has norm `1`. -/
def unitarySeq (V : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ) (g : H) :
    BoundedMatrixSequence (Idx Y) :=
  ⟨fun n ↦ (V n g : Matrix (Y n) (Y n) ℂ),
    memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact le_of_eq (CStarRing.norm_of_mem_unitary (V n g).2)⟩⟩

omit [Group H] in
@[simp] theorem unitarySeq_apply (V : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (g : H) (n : ℕ) :
    (unitarySeq Y V g : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n
      = (V n g : Matrix (Y n) (Y n) ℂ) := rfl

omit [Group H] in
theorem unitarySeq_star_mul (V : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ) (g : H)
    (n : ℕ) :
    ((unitarySeq Y V g : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)ᴴ
        * ((unitarySeq Y V g : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n) = 1 :=
  Unitary.star_mul_self_of_mem (V n g).2

theorem unitarySeq_one_of_hom (V : H →* ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    unitarySeq Y (fun n g ↦ V g n) (1 : H) = 1 := by
  refine Subtype.ext (funext fun n ↦ ?_)
  show (V 1 n : Matrix (Y n) (Y n) ℂ) = 1
  rw [map_one]
  rfl

theorem unitarySeq_mul_of_hom (V : H →* ∀ n, Matrix.unitaryGroup (Y n) ℂ)
    (g h : H) :
    unitarySeq Y (fun n g ↦ V g n) (g * h)
      = unitarySeq Y (fun n g ↦ V g n) g * unitarySeq Y (fun n g ↦ V g n) h := by
  refine Subtype.ext (funext fun n ↦ ?_)
  show (V (g * h) n : Matrix (Y n) (Y n) ℂ) = (V g n : _) * (V h n : _)
  rw [map_mul]
  rfl

/-- **`π(g) = [V_{g,n}]_ω` is a unitary representation of `H` on `H_ω`.**

This is the printed clause "the classes `π(g) = [V_{g,n}]_ω` define a unitary
representation of `H̄` on `H_ω`", for a strictly multiplicative family.  The
asymptotic case is `actQ_eq_of_sub_null` away: see below. -/
def rep (V : H →* ∀ n, Matrix.unitaryGroup (Y n) ℂ) :
    H →* (VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω) where
  toFun g :=
    actIsometryEquiv Y ω (unitarySeq Y (fun n g ↦ V g n) g)
      (unitarySeq Y (fun n g ↦ V g n) g⁻¹)
      (by rw [← unitarySeq_mul_of_hom, mul_inv_cancel, unitarySeq_one_of_hom])
      (by rw [← unitarySeq_mul_of_hom, inv_mul_cancel, unitarySeq_one_of_hom])
      (unitarySeq_star_mul Y (fun n g ↦ V g n) g)
  map_one' := by
    refine LinearIsometryEquiv.toLinearEquiv_injective (LinearEquiv.toLinearMap_injective ?_)
    show actQ Y ω (unitarySeq Y (fun n g ↦ V g n) 1) = LinearMap.id
    rw [unitarySeq_one_of_hom, actQ_one]
  map_mul' g h := by
    refine LinearIsometryEquiv.toLinearEquiv_injective (LinearEquiv.toLinearMap_injective ?_)
    show actQ Y ω (unitarySeq Y (fun n g ↦ V g n) (g * h))
      = (actQ Y ω (unitarySeq Y (fun n g ↦ V g n) g)).comp
          (actQ Y ω (unitarySeq Y (fun n g ↦ V g n) h))
    rw [unitarySeq_mul_of_hom, actQ_mul]

@[simp] theorem rep_apply (V : H →* ∀ n, Matrix.unitaryGroup (Y n) ℂ) (g : H)
    (x : VecOmega Y ω) :
    rep Y ω V g x = actQ Y ω (unitarySeq Y (fun n g ↦ V g n) g) x := rfl

/-- **The asymptotic case.**  If the family is only operator-norm
asymptotically multiplicative along `ω` -- which is what an operator-norm
asymptotic representation gives, and what `thm:normal-kazhdan` has -- the
classes are still *exactly* multiplicative, because the defect is null and a
null class acts as zero. -/
theorem actQ_unitarySeq_mul_of_asymptotic
    (V : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ) (g h : H)
    (hgh : IsNullMatrixSequence (Idx Y) (ω : Filter ℕ)
      (unitarySeq Y V (g * h) - unitarySeq Y V g * unitarySeq Y V h)) :
    actQ Y ω (unitarySeq Y V (g * h))
      = (actQ Y ω (unitarySeq Y V g)).comp (actQ Y ω (unitarySeq Y V h)) := by
  rw [actQ_eq_of_sub_null Y ω hgh, actQ_mul]

/-! ### The manuscript's hypothesis, not a stronger one

`rep` above wants the coordinate family to be a homomorphism on the nose.  What
`thm:normal-kazhdan` has is weaker and is the whole point of passing to `ω`: the
`V_{g,n}` are an operator-norm asymptotic representation, so the coordinate
multiplication defects only *vanish along* `ω`, and it is the classes that
multiply exactly.  `OmegaUnitaryRep` is that hypothesis, and `rep'` is the
printed `π` built from it.

Unitality is not assumed.  `V_{1,n}` need not be the identity matrix, and the
printed proof does not say it is; what makes `π(1) = 1` is that `π(1)` is an
idempotent isometry, and an isometry is injective. -/

/-- **An `ω`-multiplicative family of coordinate unitaries**: the manuscript's
`V_{g,n}`, with the multiplication defect null along `ω` rather than zero. -/
structure OmegaUnitaryRep (G : Type*) [Group G] where
  /-- The coordinate unitaries. -/
  V : ∀ n, G → Matrix.unitaryGroup (Y n) ℂ
  /-- The multiplication defect is null along `ω`. -/
  mul_null : ∀ g h : G, IsNullMatrixSequence (Idx Y) (ω : Filter ℕ)
    (unitarySeq Y V (g * h) - unitarySeq Y V g * unitarySeq Y V h)

namespace OmegaUnitaryRep

variable {Y} {ω} {G : Type*} [Group G]

/-- `π(g)`, before it is known to be invertible. -/
def op (R : OmegaUnitaryRep Y ω G) (g : G) :
    VecOmega Y ω →ₗ[ℂ] VecOmega Y ω :=
  actQ Y ω (unitarySeq Y R.V g)

theorem norm_op (R : OmegaUnitaryRep Y ω G) (g : G) (x : VecOmega Y ω) :
    ‖R.op g x‖ = ‖x‖ :=
  norm_actQ_of_unitary Y ω (unitarySeq_star_mul Y R.V g) x

theorem op_injective (R : OmegaUnitaryRep Y ω G) (g : G) :
    Function.Injective (R.op g) := by
  intro x y hxy
  have h : ‖R.op g (x - y)‖ = ‖x - y‖ := R.norm_op g (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)

theorem op_mul (R : OmegaUnitaryRep Y ω G) (g h : G) :
    R.op (g * h) = (R.op g).comp (R.op h) :=
  actQ_unitarySeq_mul_of_asymptotic Y ω R.V g h (R.mul_null g h)

/-- **`π(1) = 1`, without assuming `V_{1,n} = 1`.**  `π(1)` is idempotent by the
defect at `(1, 1)` and injective because it is an isometry. -/
theorem op_one (R : OmegaUnitaryRep Y ω G) : R.op (1 : G) = LinearMap.id := by
  have hidem := R.op_mul (1 : G) 1
  rw [mul_one] at hidem
  refine LinearMap.ext fun x ↦ ?_
  have hx : R.op (1 : G) (R.op (1 : G) x) = R.op (1 : G) x := by
    rw [← LinearMap.comp_apply, ← hidem]
  exact R.op_injective 1 hx

theorem op_comp_op_inv (R : OmegaUnitaryRep Y ω G) (g : G) :
    (R.op g).comp (R.op g⁻¹) = LinearMap.id := by
  rw [← R.op_mul, mul_inv_cancel, R.op_one]

theorem op_inv_comp_op (R : OmegaUnitaryRep Y ω G) (g : G) :
    (R.op g⁻¹).comp (R.op g) = LinearMap.id := by
  rw [← R.op_mul, inv_mul_cancel, R.op_one]

/-- `π(g)` as a surjective linear isometry of `H_ω`. -/
def equiv (R : OmegaUnitaryRep Y ω G) (g : G) :
    VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω where
  toLinearEquiv :=
    LinearEquiv.ofLinear (R.op g) (R.op g⁻¹) (R.op_comp_op_inv g) (R.op_inv_comp_op g)
  norm_map' := R.norm_op g

@[simp] theorem equiv_apply (R : OmegaUnitaryRep Y ω G) (g : G) (x : VecOmega Y ω) :
    R.equiv g x = R.op g x := rfl

/-- **`π(g) = [V_{g,n}]_ω` is a unitary representation of `G` on `H_ω`, from the
manuscript's asymptotic hypothesis.**

This is the printed clause of `\ref{thm:normal-kazhdan}` -- "the classes
`π(g) = [V_{g,n}]_ω` define a unitary representation of `H̄` on `H_ω`" -- with
the hypothesis the manuscript actually supplies. -/
def rep' (R : OmegaUnitaryRep Y ω G) :
    G →* (VecOmega Y ω ≃ₗᵢ[ℂ] VecOmega Y ω) where
  toFun := R.equiv
  map_one' := by
    refine LinearIsometryEquiv.toLinearEquiv_injective
      (LinearEquiv.toLinearMap_injective ?_)
    exact R.op_one
  map_mul' g h := by
    refine LinearIsometryEquiv.toLinearEquiv_injective
      (LinearEquiv.toLinearMap_injective ?_)
    exact R.op_mul g h

@[simp] theorem rep'_apply (R : OmegaUnitaryRep Y ω G) (g : G) (x : VecOmega Y ω) :
    R.rep' g x = R.op g x := rfl

end OmegaUnitaryRep

end Representation

end

end VectorOmegaAction
end GroupApproximation
