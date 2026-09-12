import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.ShulmanTraceClasses
import GroupApproximation.Sofic.UltrafilterLimit

/-!
# The ultralimit tracial state of a `C*` reduced product

`lem:tensor-sync` of `mf_recognition_complexity.tex` puts, for a free
ultrafilter `ω`,

```text
  T([(x_n)_n]) = lim_ω (τ_1 ⊗ tr_{k_n})(x_n)
```

and justifies traciality in one clause:

> `T` is a tracial state on `E` because
> `|(τ_1 ⊗ tr_{k_n})(x_n)| ≤ ‖x_n‖`.

This module carries out that clause once and for all: given a tracial state
`τ_n` on each coordinate algebra `B_n` and the printed contractivity bound
`|τ_n(x)| ≤ ‖x‖`, the coordinate traces of a bounded sequence converge along
every ultrafilter, the limit kills the null ideal `⊕_n B_n`, and the induced
functional on `∏_n B_n / ⊕_n B_n` is a tracial state.

The repository already has the analogous object for *matrix* coordinates
(`TracialUltraproduct.ultratrace`, packaged as
`HNNCoronaConjugatorSentenceAudit.normMatrixCoronaTracialState`).  That
construction is tied to the Hilbert--Schmidt null ideal of matrix sequences
and does not apply to the coordinates `B'_n = A_1 ⊗ M_{k_n}(ℂ)` of the
tensor-synchronization proof, whose coefficient algebra `A_1` is arbitrary.

The functional is defined by choosing a bounded lift, so that no defeq between
the `Submodule` and `AddSubgroup` quotient towers is ever needed; the choice is
harmless because `seqCoronaTrace_congr` shows any two lifts agree.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TensorSynchronization

open Filter PolarLiftingGeneralCStar
open scoped ComplexOrder

noncomputable section

universe u

/-! ## An ultralimit of nonnegative complex numbers is nonnegative -/

/-- The closed positive cone of `ℂ` is preserved by ultralimits.  This is the
complex counterpart of `UltrafilterLimit.ulim_nonneg`, which is stated for real
families only. -/
theorem ulim_nonneg_complex {om : Ultrafilter ℕ} {f : ℕ → ℂ}
    (hf : ∃ L : ℂ, Tendsto f (om : Filter ℕ) (nhds L))
    (h : ∀ n, 0 ≤ f n) : 0 ≤ UltrafilterLimit.ulim om f := by
  have hlim := UltrafilterLimit.tendsto_ulim hf
  have hre : Tendsto (fun n ↦ (f n).re) (om : Filter ℕ)
      (nhds (UltrafilterLimit.ulim om f).re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  have him : Tendsto (fun n ↦ (f n).im) (om : Filter ℕ)
      (nhds (UltrafilterLimit.ulim om f).im) :=
    (Complex.continuous_im.tendsto _).comp hlim
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · exact ge_of_tendsto' hre fun n ↦ (Complex.nonneg_iff.mp (h n)).1
  · refine (tendsto_nhds_unique him ?_).symm
    refine tendsto_const_nhds.congr fun n ↦ ?_
    exact (Complex.nonneg_iff.mp (h n)).2

/-! ## The ultralimit of the coordinate traces on bounded sequences -/

section Sequences

variable (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)]

/-- `lim_ω τ_n(x_n)`, the printed ultralimit of the coordinate traces of a
bounded sequence. -/
def seqCoronaTrace (tau : ∀ n, TracialState (B n)) (om : Ultrafilter ℕ)
    (a : BoundedCStarSequence B) : ℂ :=
  UltrafilterLimit.ulim om fun n ↦ tau n (a n)

/-- The printed inequality `|τ_n(x_n)| ≤ ‖x_n‖` bounds the coordinate traces
of a bounded sequence by its uniform norm, so they converge along every
ultrafilter. -/
theorem exists_tendsto_coordTrace (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (a : BoundedCStarSequence B) :
    ∃ L : ℂ, Tendsto (fun n ↦ tau n (a n)) (om : Filter ℕ) (nhds L) :=
  UltrafilterLimit.exists_tendsto_of_bounded om (C := ‖a‖) fun n ↦
    (htau n (a n)).trans (boundedCStarSequence_coord_norm_le B a n)

theorem tendsto_seqCoronaTrace (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (a : BoundedCStarSequence B) :
    Tendsto (fun n ↦ tau n (a n)) (om : Filter ℕ)
      (nhds (seqCoronaTrace B tau om a)) :=
  UltrafilterLimit.tendsto_ulim (exists_tendsto_coordTrace B tau htau om a)

theorem seqCoronaTrace_zero (tau : ∀ n, TracialState (B n))
    (om : Ultrafilter ℕ) :
    seqCoronaTrace B tau om (0 : BoundedCStarSequence B) = 0 := by
  refine UltrafilterLimit.ulim_eq ?_
  refine tendsto_const_nhds.congr fun n ↦ ?_
  exact ((tau n).map_zero).symm

theorem seqCoronaTrace_add (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (a b : BoundedCStarSequence B) :
    seqCoronaTrace B tau om (a + b) =
      seqCoronaTrace B tau om a + seqCoronaTrace B tau om b := by
  refine UltrafilterLimit.ulim_eq ?_
  refine ((tendsto_seqCoronaTrace B tau htau om a).add
    (tendsto_seqCoronaTrace B tau htau om b)).congr fun n ↦ ?_
  exact ((tau n).map_add (a n) (b n)).symm

theorem seqCoronaTrace_sub (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (a b : BoundedCStarSequence B) :
    seqCoronaTrace B tau om (a - b) =
      seqCoronaTrace B tau om a - seqCoronaTrace B tau om b := by
  refine UltrafilterLimit.ulim_eq ?_
  refine ((tendsto_seqCoronaTrace B tau htau om a).sub
    (tendsto_seqCoronaTrace B tau htau om b)).congr fun n ↦ ?_
  exact ((tau n).map_sub (a n) (b n)).symm

theorem seqCoronaTrace_smul (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (c : ℂ) (a : BoundedCStarSequence B) :
    seqCoronaTrace B tau om (c • a) = c * seqCoronaTrace B tau om a := by
  refine UltrafilterLimit.ulim_eq ?_
  refine (tendsto_const_nhds.mul
    (tendsto_seqCoronaTrace B tau htau om a)).congr fun n ↦ ?_
  have h := (tau n).map_smul c (a n)
  rw [smul_eq_mul] at h
  exact h.symm

theorem seqCoronaTrace_one (tau : ∀ n, TracialState (B n))
    [∀ n, Nontrivial (B n)] (om : Ultrafilter ℕ) :
    seqCoronaTrace B tau om (1 : BoundedCStarSequence B) = 1 := by
  refine UltrafilterLimit.ulim_eq ?_
  refine tendsto_const_nhds.congr fun n ↦ ?_
  exact ((tau n).apply_one).symm

theorem seqCoronaTrace_mul_comm (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (a b : BoundedCStarSequence B) :
    seqCoronaTrace B tau om (a * b) = seqCoronaTrace B tau om (b * a) := by
  refine UltrafilterLimit.ulim_eq ?_
  refine (tendsto_seqCoronaTrace B tau htau om (b * a)).congr fun n ↦ ?_
  exact (tau n).map_mul_comm (b n) (a n)

theorem seqCoronaTrace_star_mul_self_nonneg (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (a : BoundedCStarSequence B) :
    0 ≤ seqCoronaTrace B tau om (star a * a) := by
  refine ulim_nonneg_complex
    (exists_tendsto_coordTrace B tau htau om (star a * a)) fun n ↦ ?_
  exact (tau n).map_star_mul_self_nonneg (a n)

/-- **The ultralimit trace kills `⊕_n B_n`.**  This is the printed
contractivity `|τ_n(x_n)| ≤ ‖x_n‖` again: a sequence whose coordinate norms
tend to zero has coordinate traces tending to zero. -/
theorem seqCoronaTrace_eq_zero_of_null (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (hle : (om : Filter ℕ) ≤ cofinite) (a : BoundedCStarSequence B)
    (ha : IsNullCStarSequence B cofinite a) :
    seqCoronaTrace B tau om a = 0 := by
  refine UltrafilterLimit.ulim_eq ?_
  refine squeeze_zero_norm (fun n ↦ htau n (a n)) ?_
  have ha' : Tendsto (fun n ↦ ‖a n‖) cofinite (nhds 0) := ha
  exact ha'.mono_left hle

end Sequences

/-! ## The tracial state on the reduced product -/

section Corona

variable (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]

/-- Two bounded lifts of the same class of `∏_n B_n / ⊕_n B_n` have the same
ultralimit trace. -/
theorem seqCoronaTrace_congr (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (hle : (om : Filter ℕ) ≤ cofinite) (a b : BoundedCStarSequence B)
    (hab : cStarProductCoronaQuotient B cofinite a =
      cStarProductCoronaQuotient B cofinite b) :
    seqCoronaTrace B tau om a = seqCoronaTrace B tau om b := by
  have hzero : cStarProductCoronaQuotient B cofinite (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hnull : IsNullCStarSequence B cofinite (a - b) :=
    (cStarProductCoronaQuotient_eq_zero_iff B cofinite (a - b)).mp hzero
  have h := seqCoronaTrace_eq_zero_of_null B tau htau om hle (a - b) hnull
  have hsub := seqCoronaTrace_sub B tau htau om a b
  rw [h] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- `T([(x_n)_n]) = lim_ω τ_n(x_n)`, defined through a chosen bounded lift. -/
def coronaTrace (tau : ∀ n, TracialState (B n)) (om : Ultrafilter ℕ)
    (x : CStarProductCorona B cofinite) : ℂ :=
  seqCoronaTrace B tau om
    (cStarProductCoronaQuotient_surjective B cofinite x).choose

theorem coronaTrace_mk (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (hle : (om : Filter ℕ) ≤ cofinite) (a : BoundedCStarSequence B) :
    coronaTrace B tau om (cStarProductCoronaQuotient B cofinite a) =
      seqCoronaTrace B tau om a := by
  refine seqCoronaTrace_congr B tau htau om hle _ a ?_
  exact (cStarProductCoronaQuotient_surjective B cofinite
    (cStarProductCoronaQuotient B cofinite a)).choose_spec

/-- **The printed tracial state `T` of `lem:tensor-sync`.**  "`T` is a tracial
state on `E` because `|(τ_1 ⊗ tr_{k_n})(x_n)| ≤ ‖x_n‖`." -/
def coronaTracialState (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (hle : (om : Filter ℕ) ≤ cofinite) :
    TracialState (CStarProductCorona B cofinite) where
  toLinearMap :=
    { toFun := coronaTrace B tau om
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := cStarProductCoronaQuotient_surjective B cofinite x
        obtain ⟨b, rfl⟩ := cStarProductCoronaQuotient_surjective B cofinite y
        rw [← map_add (cStarProductCoronaQuotient B cofinite) a b]
        simp only [coronaTrace_mk B tau htau om hle]
        exact seqCoronaTrace_add B tau htau om a b
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := cStarProductCoronaQuotient_surjective B cofinite x
        rw [← map_smul (cStarProductCoronaQuotient B cofinite) c a]
        simp only [coronaTrace_mk B tau htau om hle, RingHom.id_apply,
          smul_eq_mul]
        exact seqCoronaTrace_smul B tau htau om c a }
  map_one := by
    show coronaTrace B tau om (1 : CStarProductCorona B cofinite) = 1
    rw [← map_one (cStarProductCoronaQuotient B cofinite),
      coronaTrace_mk B tau htau om hle]
    exact seqCoronaTrace_one B tau om
  map_star_mul_self_nonneg := by
    intro x
    obtain ⟨a, rfl⟩ := cStarProductCoronaQuotient_surjective B cofinite x
    show (0 : ℂ) ≤ coronaTrace B tau om
      (star (cStarProductCoronaQuotient B cofinite a) *
        cStarProductCoronaQuotient B cofinite a)
    rw [← map_star (cStarProductCoronaQuotient B cofinite) a,
      ← map_mul (cStarProductCoronaQuotient B cofinite) (star a) a,
      coronaTrace_mk B tau htau om hle]
    exact seqCoronaTrace_star_mul_self_nonneg B tau htau om a
  map_mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := cStarProductCoronaQuotient_surjective B cofinite x
    obtain ⟨b, rfl⟩ := cStarProductCoronaQuotient_surjective B cofinite y
    show coronaTrace B tau om
        (cStarProductCoronaQuotient B cofinite a *
          cStarProductCoronaQuotient B cofinite b) =
      coronaTrace B tau om
        (cStarProductCoronaQuotient B cofinite b *
          cStarProductCoronaQuotient B cofinite a)
    rw [← map_mul (cStarProductCoronaQuotient B cofinite) a b,
      ← map_mul (cStarProductCoronaQuotient B cofinite) b a]
    simp only [coronaTrace_mk B tau htau om hle]
    exact seqCoronaTrace_mul_comm B tau htau om a b

theorem coronaTracialState_mk (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (hle : (om : Filter ℕ) ≤ cofinite) (a : BoundedCStarSequence B) :
    coronaTracialState B tau htau om hle
        (cStarProductCoronaQuotient B cofinite a) =
      seqCoronaTrace B tau om a :=
  coronaTrace_mk B tau htau om hle a

/-- **The vanishing criterion for `T`.**  A bounded sequence whose coordinate
traces vanish for all large `n` has ultralimit trace zero.  This is the exact
shape of the printed case split "`β_n(q) ≠ 1` for all large `n`, the regular
representation of a finite group has trace zero off the identity, and again
`T(V(1,q)) = 0`". -/
theorem coronaTracialState_eq_zero_of_eventually
    (tau : ∀ n, TracialState (B n))
    (htau : ∀ (n : ℕ) (x : B n), ‖tau n x‖ ≤ ‖x‖) (om : Ultrafilter ℕ)
    (hle : (om : Filter ℕ) ≤ cofinite) (a : BoundedCStarSequence B)
    (h : ∀ᶠ n in cofinite, tau n (a n) = 0) :
    coronaTracialState B tau htau om hle
      (cStarProductCoronaQuotient B cofinite a) = 0 := by
  rw [coronaTracialState_mk B tau htau om hle a]
  refine UltrafilterLimit.ulim_eq ?_
  have hom : ∀ᶠ n in (om : Filter ℕ), tau n (a n) = 0 := h.filter_mono hle
  have heq : (fun _ : ℕ ↦ (0 : ℂ)) =ᶠ[(om : Filter ℕ)]
      fun n ↦ tau n (a n) := hom.mono fun n hn ↦ hn.symm
  exact tendsto_const_nhds.congr' heq

end Corona

end

end TensorSynchronization
end MFRecognition
end Manuscript
end GroupApproximation
