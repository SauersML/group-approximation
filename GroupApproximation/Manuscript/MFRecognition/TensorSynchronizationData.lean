import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationCoronaTrace
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# `lem:tensor-sync`: the coordinate algebra, the representation `V` and the trace `T`

This module formalizes the first paragraph of the printed proof of
`lem:tensor-sync` in `mf_recognition_complexity.tex`:

> Let `E_n` be the image of `(λ_n, β_n) : Γ × Q → G_n × B_n`, a finite group of
> order `k_n`, and let `L_n` be its left regular representation on `ℓ²(E_n)`.
> Put `B'_n = A_1 ⊗ M_{k_n}(ℂ)`, which is MF by Lemma
> (reduced products of MF algebras), let `E = ∏_n B'_n / ⊕_n B'_n`, and define
> `V(g,q) = [(ρ_1(g) ⊗ L_n(λ_n(g), β_n(q)))_n]`,
> `T([(x_n)_n]) = lim_ω (τ_1 ⊗ tr_{k_n})(x_n)`, for a free ultrafilter `ω`.
> Each coordinate of `V` is a homomorphism into a unitary group, so `V` is a
> homomorphism, and `T` is a tracial state on `E` because
> `|(τ_1 ⊗ tr_{k_n})(x_n)| ≤ ‖x_n‖`.  If `g ≠ 1` then `τ_1(ρ_1(g)) = 0`, so
> `T(V(g,q)) = 0`; if `g = 1` and `q ≠ 1` then `β_n(q) ≠ 1` for all large `n`,
> the regular representation of a finite group has trace zero off the identity,
> and again `T(V(1,q)) = 0`.

The tensor product `A_1 ⊗ M_{k_n}(ℂ)` is taken in the repository's existing
coefficient-matrix model `CStarMatrix (E n) (E n) A_1`, in which
`ρ_1(g) ⊗ L_n(e)` is the weighted permutation matrix
`TensorSynchronizationAssembly.finiteProductTensorHom` and `τ_1 ⊗ tr_{k_n}` is
the normalized diagonal amplification
`TensorSynchronizationAssembly.matrixTracialState`.

The finite groups `E_n` and the coordinate maps `ell n : Γ × Q →* E_n` are
kept abstract here, subject to the one printed property they are used through
(`β_n(q) ≠ 1` for all large `n` detects `q ≠ 1` in `E_n`); the printed image of
`(λ_n, β_n)` is substituted in `TensorSynchronization.lean`.
-/

-- The normalized diagonal amplification `matrixTracialState` sits in the
-- `TensorSynchronizationAssembly` namespace of the one-sided lane, and that
-- lane is in the middle of splitting its assembly module into cores, which
-- moves the declaration to a `TensorSynchronizationMatrixCore` namespace.
-- Registering the second namespace here (it is empty in the unsplit layout)
-- makes the `open` below legal, and therefore this file correct, under either
-- layout.  Nothing is declared in it.
namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore
end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TensorSynchronization

open Filter PolarLiftingGeneralCStar
open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
open GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore
open scoped ComplexOrder InnerProductSpace

noncomputable section

noncomputable local instance tensorSynchronizationDataPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorSynchronizationDataStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-! ## Two elementary facts about tracial states -/

/-- A unital functional separates `1` from `0`, so an algebra carrying a
tracial state is nontrivial. -/
theorem nontrivial_of_tracialState {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] (tau : TracialState A) : Nontrivial A := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have hone := tau.apply_one
  rw [h, tau.map_zero] at hone
  exact zero_ne_one hone

/-- A tracial state, regarded as a positive linear functional for the spectral
order. -/
def tracialStatePositiveLinearMap {A : Type*} [CStarAlgebra A]
    (tau : TracialState A) : A →ₚ[ℂ] ℂ :=
  { tau.toLinearMap with
    monotone' := by
      intro x y hxy
      rw [StarOrderedRing.le_iff] at hxy
      obtain ⟨p, hp, rfl⟩ := hxy
      have hp0 : (0 : ℂ) ≤ tau p := by
        induction hp using AddSubmonoid.closure_induction with
        | mem s hs =>
            obtain ⟨w, rfl⟩ := hs
            exact tau.map_star_mul_self_nonneg w
        | zero => simp
        | add c d hc hd hc0 hd0 =>
            rw [map_add]
            exact add_nonneg hc0 hd0
      show tau x ≤ tau (x + p)
      rw [map_add]
      exact le_add_of_nonneg_right hp0 }

@[simp] theorem tracialStatePositiveLinearMap_apply
    {A : Type*} [CStarAlgebra A] (tau : TracialState A) (x : A) :
    tracialStatePositiveLinearMap tau x = tau x :=
  rfl

/-- Every tracial state on a unital C-star algebra is contractive.  The proof
is the GNS Cauchy--Schwarz estimate against the class of `1`.

The two GNS vectors are spelled out rather than named by `let`:
`PositiveLinearMap.preGNS_norm_sq` reads
`(‖v‖ : ℂ)^2 = f (star (ofPreGNS v) * ofPreGNS v)`, and the rewrite by
`ofPreGNS_toPreGNS` has to see `ofPreGNS (toPreGNS a)` syntactically.  This is
the idiom of `Analysis/GNSEigenvector.norm_gnsCyclic`. -/
theorem norm_tracialState_le {A : Type*} [CStarAlgebra A]
    (tau : TracialState A) (x : A) : ‖tau x‖ ≤ ‖x‖ := by
  let f := tracialStatePositiveLinearMap tau
  have hfeq : ∀ a : A, f a = tau a := fun _ ↦ rfl
  have hf1 : f (1 : A) = 1 := by
    rw [hfeq]
    exact tau.apply_one
  -- `⟪[1], [x]⟫ = τ(x)`.
  have hinner : ⟪(f.toPreGNS 1 : f.PreGNS), (f.toPreGNS x : f.PreGNS)⟫_ℂ
      = tau x := by
    rw [PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS,
      PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul]
    exact hfeq x
  -- `‖[1]‖ = 1`, because `τ(1) = 1`.
  have hone : ‖(f.toPreGNS 1 : f.PreGNS)‖ = 1 := by
    have hsq := f.preGNS_norm_sq (f.toPreGNS 1)
    rw [f.ofPreGNS_toPreGNS, star_one, one_mul, hf1] at hsq
    have hone_sq : ‖(f.toPreGNS 1 : f.PreGNS)‖ ^ 2 = 1 := by
      exact_mod_cast hsq
    have h4 : (‖(f.toPreGNS 1 : f.PreGNS)‖ - 1)
        * (‖(f.toPreGNS 1 : f.PreGNS)‖ + 1) = 0 := by
      calc (‖(f.toPreGNS 1 : f.PreGNS)‖ - 1)
            * (‖(f.toPreGNS 1 : f.PreGNS)‖ + 1)
          = ‖(f.toPreGNS 1 : f.PreGNS)‖ ^ 2 - 1 := by ring
        _ = 0 := by rw [hone_sq]; ring
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · linarith [norm_nonneg (f.toPreGNS 1 : f.PreGNS)]
  -- `‖[x]‖² = τ(x*x) ≤ ‖x*x‖ = ‖x‖²`.
  have hx_sq : ((‖(f.toPreGNS x : f.PreGNS)‖ : ℝ) : ℂ) ^ 2
      = f (star x * x) := by
    have hsq := f.preGNS_norm_sq (f.toPreGNS x)
    rwa [f.ofPreGNS_toPreGNS] at hsq
  have hx_order : star x * x ≤ algebraMap ℝ A ‖star x * x‖ :=
    (IsSelfAdjoint.star_mul_self x).le_algebraMap_norm_self
  have hfx_scalar : f (algebraMap ℝ A ‖star x * x‖)
      = ((‖star x * x‖ : ℝ) : ℂ) := by
    have halg : algebraMap ℝ A ‖star x * x‖
        = ((‖star x * x‖ : ℝ) : ℂ) • (1 : A) := by
      rw [Algebra.algebraMap_eq_smul_one,
        ← algebraMap_smul ℂ (‖star x * x‖ : ℝ) (1 : A)]
      congr 1
    rw [hfeq, halg, tau.map_smul, tau.apply_one, smul_eq_mul, mul_one]
  have hfx_order : ((‖(f.toPreGNS x : f.PreGNS)‖ ^ 2 : ℝ) : ℂ)
      ≤ ((‖star x * x‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow, hx_sq, ← hfx_scalar]
    exact f.monotone hx_order
  have hx_norm : ‖(f.toPreGNS x : f.PreGNS)‖ ≤ ‖x‖ := by
    have hreal : ‖(f.toPreGNS x : f.PreGNS)‖ ^ 2 ≤ ‖star x * x‖ := by
      exact (RCLike.ofReal_le_ofReal (K := ℂ)).mp hfx_order
    rw [CStarRing.norm_star_mul_self] at hreal
    nlinarith [norm_nonneg (f.toPreGNS x : f.PreGNS), norm_nonneg x]
  calc
    ‖tau x‖ = ‖⟪(f.toPreGNS 1 : f.PreGNS), (f.toPreGNS x : f.PreGNS)⟫_ℂ‖ := by
      rw [hinner]
    _ ≤ ‖(f.toPreGNS 1 : f.PreGNS)‖ * ‖(f.toPreGNS x : f.PreGNS)‖ :=
      norm_inner_le_norm _ _
    _ = ‖(f.toPreGNS x : f.PreGNS)‖ := by rw [hone, one_mul]
    _ ≤ ‖x‖ := hx_norm

/-- **The printed inequality `|(τ_1 ⊗ tr_{k_n})(x_n)| ≤ ‖x_n‖`.**  This is the
one estimate quoted in the proof of `lem:tensor-sync` to see that `T` is a
state and not merely a linear functional. -/
theorem norm_matrixTracialState_le {A : Type*} [CStarAlgebra A]
    (tau : TracialState A) (I : Type*) [Fintype I] [DecidableEq I]
    (hI : Nonempty I) (M : CStarMatrix I I A) :
    ‖matrixTracialState tau I hI M‖ ≤ ‖M‖ :=
  norm_tracialState_le (matrixTracialState tau I hI) M

/-! ## The free ultrafilter of the printed limit -/

/-- The free ultrafilter `ω` of the printed formula `T = lim_ω`. -/
def syncUltrafilter : Ultrafilter ℕ :=
  Ultrafilter.of cofinite

theorem syncUltrafilter_le_cofinite :
    (syncUltrafilter : Filter ℕ) ≤ cofinite :=
  Ultrafilter.of_le cofinite

/-! ## The coordinate algebras `B'_n = A_1 ⊗ M_{k_n}(ℂ)` -/

/-- `E_n` is a group, hence nonempty; this is the `Nonempty` argument of every
normalized diagonal trace below. -/
theorem coordNonempty (E : ℕ → Type) [∀ n, Group (E n)] (n : ℕ) :
    Nonempty (E n) :=
  ⟨1⟩

section Coordinates

variable {Gamma : Type} [Group Gamma] {Q : Type} [Group Q]
  {A1 : Type} [CStarAlgebra A1]
  (E : ℕ → Type) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
  [∀ n, DecidableEq (E n)]

/-- `τ_1 ⊗ tr_{k_n}`, the normalized diagonal amplification of `τ_1` to
`B'_n = A_1 ⊗ M_{k_n}(ℂ)`. -/
def coordTracialState (tau1 : TracialState A1) (n : ℕ) :
    TracialState (CStarMatrix (E n) (E n) A1) :=
  matrixTracialState tau1 (E n) (coordNonempty E n)

/-- The printed inequality `|(τ_1 ⊗ tr_{k_n})(x_n)| ≤ ‖x_n‖`, at the
coordinate algebras. -/
theorem coordTracialState_norm_le (tau1 : TracialState A1) (n : ℕ)
    (x : CStarMatrix (E n) (E n) A1) :
    ‖coordTracialState E tau1 n x‖ ≤ ‖x‖ :=
  norm_matrixTracialState_le tau1 (E n) (coordNonempty E n) x

/-- Each coordinate algebra `B'_n` is nontrivial, because it carries the
tracial state `τ_1 ⊗ tr_{k_n}`. -/
theorem coordAlgebra_nontrivial (tau1 : TracialState A1) (n : ℕ) :
    Nontrivial (CStarMatrix (E n) (E n) A1) :=
  nontrivial_of_tracialState (coordTracialState E tau1 n)

/-- `ρ_1(g) ⊗ L_n(λ_n(g), β_n(q))`, the `n`-th coordinate of the printed
representation `V`. -/
def coordRep (R1 : RegularRealizationData Gamma A1)
    (ell : ∀ n, Gamma × Q →* E n) (n : ℕ) :
    Gamma × Q →* unitary (CStarMatrix (E n) (E n) A1) :=
  finiteProductTensorHom R1.rho (ell n)

/-- **The printed case split for the coordinate traces.**  "If `g ≠ 1` then
`τ_1(ρ_1(g)) = 0`, so `T(V(g,q)) = 0`; if `g = 1` and `q ≠ 1` then
`β_n(q) ≠ 1` for all large `n`, the regular representation of a finite group
has trace zero off the identity, and again `T(V(1,q)) = 0`." -/
theorem coordTrace_eventually_zero (R1 : RegularRealizationData Gamma A1)
    (ell : ∀ n, Gamma × Q →* E n)
    (hdetect : ∀ z : Gamma × Q, z.1 = 1 → z.2 ≠ 1 →
      ∀ᶠ n in cofinite, ell n z ≠ 1)
    (z : Gamma × Q) (hz : z ≠ 1) :
    ∀ᶠ n in cofinite,
      coordTracialState E R1.tau n
        ((coordRep E R1 ell n z : unitary (CStarMatrix (E n) (E n) A1)) :
          CStarMatrix (E n) (E n) A1) = 0 := by
  by_cases hz1 : z.1 = 1
  · have hz2 : z.2 ≠ 1 := fun h2 ↦ hz (Prod.ext hz1 h2)
    refine (hdetect z hz1 hz2).mono fun n hn ↦ ?_
    exact finiteProductTensorHom_trace_zero_of_finite_ne_one
      (coordNonempty E n) R1.rho R1.tau (ell n) z hn
  · refine Eventually.of_forall fun n ↦ ?_
    exact finiteProductTensorHom_trace_zero_of_first_ne_one
      (coordNonempty E n) R1 (ell n) z hz1

end Coordinates

/-! ## The reduced product `E = ∏_n B'_n / ⊕_n B'_n`, with `V` and `T` -/

section Corona

variable {Gamma : Type} [Group Gamma] {Q : Type} [Group Q]
  {A1 : Type} [CStarAlgebra A1]
  (E : ℕ → Type) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
  [∀ n, DecidableEq (E n)]
  [∀ n, Nontrivial (CStarMatrix (E n) (E n) A1)]

/-- **The printed representation `V(g,q) = [(ρ_1(g) ⊗ L_n(λ_n(g), β_n(q)))_n]`.**
"Each coordinate of `V` is a homomorphism into a unitary group, so `V` is a
homomorphism." -/
def syncRep (R1 : RegularRealizationData Gamma A1)
    (ell : ∀ n, Gamma × Q →* E n) :
    Gamma × Q →*
      unitary (CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1)
        cofinite) :=
  coordinateProductCoronaHom (fun n ↦ CStarMatrix (E n) (E n) A1)
    (coordRep E R1 ell)

/-- **The printed tracial state
`T([(x_n)_n]) = lim_ω (τ_1 ⊗ tr_{k_n})(x_n)`.** -/
def syncTrace (tau1 : TracialState A1) :
    TracialState
      (CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) :=
  coronaTracialState (fun n ↦ CStarMatrix (E n) (E n) A1)
    (coordTracialState E tau1) (coordTracialState_norm_le E tau1)
    syncUltrafilter syncUltrafilter_le_cofinite

/-- **`T(V(g,q)) = 0` for `(g,q) ≠ (1,1)`**, the conclusion of the printed
case split.  The vanishing is coordinatewise for all large `n`, and the
ultralimit of an eventually vanishing family vanishes. -/
theorem syncTrace_syncRep_eq_zero (R1 : RegularRealizationData Gamma A1)
    (ell : ∀ n, Gamma × Q →* E n)
    (hdetect : ∀ z : Gamma × Q, z.1 = 1 → z.2 ≠ 1 →
      ∀ᶠ n in cofinite, ell n z ≠ 1)
    (z : Gamma × Q) (hz : z ≠ 1) :
    syncTrace E R1.tau
      ((syncRep E R1 ell z :
        unitary (CStarProductCorona
          (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
        CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) = 0 := by
  have hV :
      ((syncRep E R1 ell z :
        unitary (CStarProductCorona
          (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
        CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) =
      cStarProductCoronaQuotient (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite
        (boundedUnitaryCStarSequence (fun n ↦ CStarMatrix (E n) (E n) A1)
          fun n ↦ coordRep E R1 ell n z) := rfl
  rw [hV]
  exact coronaTracialState_eq_zero_of_eventually
    (fun n ↦ CStarMatrix (E n) (E n) A1) (coordTracialState E R1.tau)
    (coordTracialState_norm_le E R1.tau) syncUltrafilter
    syncUltrafilter_le_cofinite _
    (coordTrace_eventually_zero E R1 ell hdetect z hz)

end Corona

end

end TensorSynchronization
end MFRecognition
end Manuscript
end GroupApproximation
