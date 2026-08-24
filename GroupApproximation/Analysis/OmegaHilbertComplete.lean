import GroupApproximation.Sofic.KOmegaHilbert
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# KT.05: `K_ω` is complete, hence a Hilbert space

`Sofic/KOmegaHilbert.lean` descends the ultralimit pairing to the manuscript's
`K_ω` and registers mathlib's `InnerProductSpace ℂ` on it, positive
definiteness included.  Its own docstring then says, and the proof ledger
records at row `KT.05`, that

> **Completeness is not proved.**  `K_ω` is a Hilbert space -- the ultraproduct
> of Hilbert spaces along an ultrafilter is complete -- but that is a separate
> diagonal argument and no `CompleteSpace` instance is claimed below.

This file supplies that missing property, so that the printed sentence of
the Kazhdan transport result,

> *The ultraproduct.*  Let `K_ω` and `B_ω = ∏_ω B(K_n)` be as in
> the former transport argument,

names a genuine Hilbert space: `K_ω` carries `InnerProductSpace ℂ` from
`KOmegaHilbert` and `CompleteSpace` from `kOmegaCompleteSpace` below, so the
steps of the printed proof that speak of the orthogonal complement of `Fix` and
of a spectral projection have their ambient available.

## The route

Not the diagonal argument.  The criterion used is
`NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`: it suffices that
every absolutely convergent series of classes converges.  Two observations make
that elementary here.

* **Truncation.**  A class `x` of `K_ω` has, for every `ε > 0`, a representative
  whose *coordinate* masses obey `matMass ξ_n ≤ (‖x‖² + ε) w_n` at **every**
  stage, not merely on a set of `ω` (`exists_rep_matMass_le`).  Truncating an
  arbitrary representative to the set where that bound holds changes it only off
  a set of `ω`, which is exactly the denominator of `K_ω`.
* **Coordinatewise summation.**  With representatives so normalized, the series
  `∑_k ξ^k_n` converges in each coordinate space, because that space is `ℓ²` on
  the doubled index and the coordinate norms admit a summable majorant
  independent of the stage up to the factor `√(w n)`.  The bounds transfer to
  the ultraproduct because `matMass ζ_n ≤ R² w_n` gives `‖[ζ_n]_ω‖ ≤ R`.

The coordinate space `M_{Y n}(ℂ)` is met here only through row-major
vectorization `hsVec` into `EuclideanSpace ℂ (Y n × Y n)`, whose norm squared is
`matMass`; that keeps the file independent of any norm instance on `Matrix`, in
particular of the scoped `Matrix.Norms.L2Operator` instances, which carry the
operator norm and not this one.
-/

namespace GroupApproximation
namespace OmegaHilbertComplete

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction
open HilbertUltraproductInner HilbertUltraproductPairing
open HilbertUltraproductSpace KOmegaHilbert ScaledKazhdanTransport

noncomputable section

/-! ## The coordinate Hilbert space `K_n`, in row-major coordinates

`K_n = M_{Y n}(ℂ)` with the unnormalized Frobenius mass is `ℓ²` on the doubled
index `Y n × Y n`.  `matMass` is the square of that norm, and nothing else about
the coordinate space is used below. -/

section Vectorization

/-! Vectorization itself needs no finiteness: `ℓ²(Z × Z)` is a type synonym for
a function type, and its additive structure is pointwise.  Finiteness enters
only with the norm, in the next section, so the section variables are split
accordingly rather than carried and `omit`ted. -/

variable {Z : Type*}

/-- Row-major vectorization of a coordinate matrix as a vector of `ℓ²(Z × Z)`. -/
def hsVec (A : Matrix Z Z ℂ) : EuclideanSpace ℂ (Z × Z) :=
  WithLp.toLp 2 fun p ↦ A p.1 p.2

/-- The matrix read off a vector of `ℓ²(Z × Z)`; inverse to `hsVec`. -/
def hsMat (v : EuclideanSpace ℂ (Z × Z)) : Matrix Z Z ℂ :=
  Matrix.of fun i j ↦ v (i, j)

@[simp] theorem hsVec_apply (A : Matrix Z Z ℂ) (p : Z × Z) :
    hsVec A p = A p.1 p.2 := rfl

@[simp] theorem hsMat_apply (v : EuclideanSpace ℂ (Z × Z)) (i j : Z) :
    hsMat v i j = v (i, j) := rfl

@[simp] theorem hsMat_hsVec (A : Matrix Z Z ℂ) : hsMat (hsVec A) = A := rfl

@[simp] theorem hsVec_hsMat (v : EuclideanSpace ℂ (Z × Z)) :
    hsVec (hsMat v) = v := by
  ext p
  rfl

theorem hsVec_add (A B : Matrix Z Z ℂ) :
    hsVec (A + B) = hsVec A + hsVec B := by
  ext p
  rfl

theorem hsMat_add (v v' : EuclideanSpace ℂ (Z × Z)) :
    hsMat (v + v') = hsMat v + hsMat v' := by
  ext i j
  rfl

/-- Vectorization as an additive equivalence, so that finite sums pass through
it by `map_sum`. -/
def hsEquiv : Matrix Z Z ℂ ≃+ EuclideanSpace ℂ (Z × Z) where
  toFun := hsVec
  invFun := hsMat
  left_inv := hsMat_hsVec
  right_inv := hsVec_hsMat
  map_add' := hsVec_add

@[simp] theorem hsEquiv_apply (A : Matrix Z Z ℂ) :
    hsEquiv (Z := Z) A = hsVec A := rfl

theorem hsVec_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix Z Z ℂ) :
    hsVec (∑ i ∈ s, f i) = ∑ i ∈ s, hsVec (f i) :=
  map_sum (hsEquiv (Z := Z)) f s

theorem hsMat_sum_hsVec {ι : Type*} (s : Finset ι) (f : ι → Matrix Z Z ℂ) :
    hsMat (∑ i ∈ s, hsVec (f i)) = ∑ i ∈ s, f i := by
  rw [← hsVec_sum, hsMat_hsVec]

end Vectorization

/-! ## The mass, as a squared norm

Finiteness of the index enters here and nowhere above: `matMass` is a finite sum
of squared entry norms, and it is exactly the squared `ℓ²` norm of the
vectorization. -/

section Mass

variable {Z : Type*} [Fintype Z]

/-- **The Frobenius mass is the squared `ℓ²` norm of the vectorization.**  This
is the only property of `hsVec` that the argument below uses. -/
theorem norm_hsVec_sq (A : Matrix Z Z ℂ) : ‖hsVec A‖ ^ 2 = matMass A := by
  have hsum : ∑ p : Z × Z, ‖hsVec A p‖ ^ 2
      = ∑ i : Z, ∑ j : Z, Complex.normSq (A i j) := by
    rw [← Fintype.sum_prod_type' (fun i j ↦ Complex.normSq (A i j))]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [hsVec_apply]
    exact (FrobeniusPairing.normSq_eq_norm_sq (A p.1 p.2)).symm
  rw [EuclideanSpace.norm_sq_eq, hsum]
  rfl

theorem norm_hsVec (A : Matrix Z Z ℂ) :
    ‖hsVec A‖ = Real.sqrt (matMass A) := by
  rw [← norm_hsVec_sq, Real.sqrt_sq (norm_nonneg _)]

theorem matMass_hsMat (v : EuclideanSpace ℂ (Z × Z)) :
    matMass (hsMat v) = ‖v‖ ^ 2 := by
  rw [← norm_hsVec_sq, hsVec_hsMat]

/-- The mass estimate in the shape the summation argument produces it: a
coordinate `ℓ²` bound of the form `R √t` gives a mass bound `R² t`. -/
theorem matMass_hsMat_le (v : EuclideanSpace ℂ (Z × Z)) {R t : ℝ} (ht : 0 ≤ t)
    (h : ‖v‖ ≤ R * Real.sqrt t) : matMass (hsMat v) ≤ R ^ 2 * t := by
  rw [matMass_hsMat]
  have h0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  calc ‖v‖ ^ 2 ≤ (R * Real.sqrt t) ^ 2 := by nlinarith [h, h0]
    _ = R ^ 2 * t := by rw [mul_pow, Real.sq_sqrt ht]

end Mass

/-! ## Classes of `K_ω`, their norms, and normalized representatives -/

section Representatives

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {ω : Ultrafilter ℕ}

@[simp] theorem mkK_zero (hw : ∀ n, 0 ≤ w n) : mkK Y w ω hw 0 = 0 := rfl

@[simp] theorem mkK_add (hw : ∀ n, 0 ≤ w n) (ξ η : massBounded Y w) :
    mkK Y w ω hw (ξ + η) = mkK Y w ω hw ξ + mkK Y w ω hw η := rfl

@[simp] theorem mkK_sub (hw : ∀ n, 0 ≤ w n) (ξ η : massBounded Y w) :
    mkK Y w ω hw (ξ - η) = mkK Y w ω hw ξ - mkK Y w ω hw η := rfl

theorem mkK_sum (hw : ∀ n, 0 ≤ w n) (s : Finset ℕ) (f : ℕ → massBounded Y w) :
    mkK Y w ω hw (∑ k ∈ s, f k) = ∑ k ∈ s, mkK Y w ω hw (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, mkK_zero]
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, mkK_add, ih]

theorem mkK_surjective (hw : ∀ n, 0 ≤ w n) (x : KOmega Y w ω hw) :
    ∃ ξ : massBounded Y w, mkK Y w ω hw ξ = x := by
  obtain ⟨ξ, hξ⟩ :=
    Submodule.Quotient.mk_surjective (nullIn Y w ω) (show Vec Y w ω from x)
  exact ⟨ξ, hξ⟩

/-- The square of the norm of a class is the ultralimit of the renormalized
coordinate masses; `norm_mkK` states the same with a square root. -/
theorem norm_mkK_sq (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w) :
    ‖mkK Y w ω hw ξ‖ ^ 2
      = ulim ω (fun n ↦ matMass ((ξ : MatFam Y) n) / w n) := by
  rw [norm_mkK]
  exact Real.sq_sqrt (ulim_nonneg (exists_tendsto_mass hw ξ)
    fun n ↦ div_nonneg (matMass_nonneg _) (hw n))

/-- **A pointwise mass bound bounds the norm of the class.**  This is the
direction of the norm formula that the summation argument consumes. -/
theorem norm_mkK_le (hw : ∀ n, 0 ≤ w n) {ζ : massBounded Y w} {R : ℝ}
    (hR : 0 ≤ R) (h : ∀ n, matMass ((ζ : MatFam Y) n) ≤ R ^ 2 * w n) :
    ‖mkK Y w ω hw ζ‖ ≤ R := by
  have hle : ulim ω (fun n ↦ matMass ((ζ : MatFam Y) n) / w n) ≤ R ^ 2 := by
    refine ulim_le (exists_tendsto_mass hw ζ) (Eventually.of_forall fun n ↦ ?_)
    rcases (hw n).lt_or_eq with hpos | hzero
    · exact (div_le_iff₀ hpos).mpr (h n)
    · rw [← hzero, div_zero]
      positivity
  calc ‖mkK Y w ω hw ζ‖
      = Real.sqrt (ulim ω (fun n ↦ matMass ((ζ : MatFam Y) n) / w n)) :=
        norm_mkK Y w ω hw ζ
    _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hle
    _ = R := Real.sqrt_sq hR

/-- **Truncation at the norm.**  Every class of `K_ω` has a representative whose
coordinate masses obey `matMass ξ_n ≤ (‖x‖² + ε) w_n` at *every* stage.

An arbitrary representative obeys the bound only on a set of `ω` -- that is what
`lim_ω matMass ξ_n / w_n = ‖x‖²` says -- and setting it to zero off that set
changes it by a family null at the weight along `ω`, which is precisely an
element of the denominator of `K_ω`.  This is the step that makes the
coordinatewise series below converge, and it is the only place the definition of
the denominator is used. -/
theorem exists_rep_matMass_le (hw : ∀ n, 0 ≤ w n) (x : KOmega Y w ω hw)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : massBounded Y w, mkK Y w ω hw ξ = x ∧
      ∀ n, matMass ((ξ : MatFam Y) n) ≤ (‖x‖ ^ 2 + ε) * w n := by
  classical
  obtain ⟨ξ₀, rfl⟩ := mkK_surjective hw x
  obtain ⟨C₀, hC₀⟩ := ξ₀.2
  have hnorm : ‖mkK Y w ω hw ξ₀‖ ^ 2
      = ulim ω (fun n ↦ matMass ((ξ₀ : MatFam Y) n) / w n) := norm_mkK_sq hw ξ₀
  have hnn : (0 : ℝ) ≤ ‖mkK Y w ω hw ξ₀‖ ^ 2 + ε :=
    add_nonneg (sq_nonneg _) hε.le
  -- the bound holds on a set of `ω`
  have hgood : ∀ᶠ n in (ω : Filter ℕ),
      matMass ((ξ₀ : MatFam Y) n)
        ≤ (‖mkK Y w ω hw ξ₀‖ ^ 2 + ε) * w n := by
    have hlt : ∀ᶠ n in (ω : Filter ℕ),
        matMass ((ξ₀ : MatFam Y) n) / w n
          < ‖mkK Y w ω hw ξ₀‖ ^ 2 + ε := by
      refine eventually_lt_of_ulim_lt (exists_tendsto_mass hw ξ₀) ?_
      rw [hnorm]
      linarith
    filter_upwards [hlt] with n hn
    rcases (hw n).lt_or_eq with hpos | hzero
    · exact (div_le_iff₀ hpos).mp hn.le
    · have hz : (ξ₀ : MatFam Y) n = 0 :=
        eq_zero_of_weight_eq_zero hC₀ hzero.symm
      have h0 : matMass ((ξ₀ : MatFam Y) n) = 0 := by rw [hz, matMass_zero]
      have hw0 : w n = 0 := hzero.symm
      simp [h0, hw0]
  -- the truncated family obeys the bound at every stage
  have hcut : ∀ n, matMass (if matMass ((ξ₀ : MatFam Y) n)
        ≤ (‖mkK Y w ω hw ξ₀‖ ^ 2 + ε) * w n then (ξ₀ : MatFam Y) n else 0)
      ≤ (‖mkK Y w ω hw ξ₀‖ ^ 2 + ε) * w n := by
    intro n
    by_cases hn : matMass ((ξ₀ : MatFam Y) n)
        ≤ (‖mkK Y w ω hw ξ₀‖ ^ 2 + ε) * w n
    · rw [if_pos hn]
      exact hn
    · rw [if_neg hn, matMass_zero]
      exact mul_nonneg hnn (hw n)
  refine ⟨⟨fun n ↦ if matMass ((ξ₀ : MatFam Y) n)
      ≤ (‖mkK Y w ω hw ξ₀‖ ^ 2 + ε) * w n then (ξ₀ : MatFam Y) n else 0,
    ⟨‖mkK Y w ω hw ξ₀‖ ^ 2 + ε, hcut⟩⟩, ?_, hcut⟩
  refine (Submodule.Quotient.eq (nullIn Y w ω)).mpr ?_
  intro δ hδ
  filter_upwards [hgood] with n hn
  show matMass ((if matMass ((ξ₀ : MatFam Y) n)
      ≤ (‖mkK Y w ω hw ξ₀‖ ^ 2 + ε) * w n then (ξ₀ : MatFam Y) n else 0)
    - (ξ₀ : MatFam Y) n) ≤ δ * clipWeight w n
  rw [if_pos hn, sub_self, matMass_zero]
  exact mul_nonneg hδ.le (clipWeight_nonneg w n)

end Representatives

/-! ## KT.05: completeness -/

section Complete

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {ω : Ultrafilter ℕ}

/-- **The absolutely convergent series criterion, verified for `K_ω`.**  Every
series of classes with summable norms converges in `K_ω`.

The limit is built coordinatewise: representatives normalized by
`exists_rep_matMass_le` have coordinate `ℓ²` norms at most
`(‖u k‖ + 2^{-k})·√(w n)`, whose sum over `k` converges, so the coordinate
series converges in `ℓ²(Y n × Y n)` and its sums form a mass-bounded family.
The tail estimate is the same bound applied to `∑_{k ≥ N}`. -/
theorem exists_tendsto_sum_of_summable_norm (hw : ∀ n, 0 ≤ w n)
    (u : ℕ → KOmega Y w ω hw) (hu : Summable fun k ↦ ‖u k‖) :
    ∃ a, Tendsto (fun N ↦ ∑ k ∈ Finset.range N, u k) atTop (𝓝 a) := by
  classical
  -- the summable majorant of the coordinate norms
  have hbnn : ∀ k : ℕ, (0 : ℝ) ≤ ‖u k‖ + (1 / 2 : ℝ) ^ k := fun k ↦ by positivity
  have hbsum : Summable fun k ↦ ‖u k‖ + (1 / 2 : ℝ) ^ k :=
    hu.add summable_geometric_two
  -- normalized representatives
  have hrep : ∀ k : ℕ, ∃ ξ : massBounded Y w, mkK Y w ω hw ξ = u k ∧
      ∀ n, matMass ((ξ : MatFam Y) n)
        ≤ (‖u k‖ + (1 / 2 : ℝ) ^ k) ^ 2 * w n := by
    intro k
    obtain ⟨ξ, hξ1, hξ2⟩ :=
      exists_rep_matMass_le hw (u k) (ε := ((1 / 2 : ℝ) ^ k) ^ 2) (by positivity)
    refine ⟨ξ, hξ1, fun n ↦ (hξ2 n).trans ?_⟩
    have hsq : ‖u k‖ ^ 2 + ((1 / 2 : ℝ) ^ k) ^ 2
        ≤ (‖u k‖ + (1 / 2 : ℝ) ^ k) ^ 2 := by
      nlinarith [norm_nonneg (u k), pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
    exact mul_le_mul_of_nonneg_right hsq (hw n)
  choose ξ hξeq hξle using hrep
  -- coordinate norms
  have hnormle : ∀ k n : ℕ, ‖hsVec ((ξ k : MatFam Y) n)‖
      ≤ (‖u k‖ + (1 / 2 : ℝ) ^ k) * Real.sqrt (w n) := by
    intro k n
    rw [norm_hsVec]
    calc Real.sqrt (matMass ((ξ k : MatFam Y) n))
        ≤ Real.sqrt ((‖u k‖ + (1 / 2 : ℝ) ^ k) ^ 2 * w n) :=
          Real.sqrt_le_sqrt (hξle k n)
      _ = (‖u k‖ + (1 / 2 : ℝ) ^ k) * Real.sqrt (w n) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (hbnn k)]
  -- coordinatewise summability
  have hsummable : ∀ n : ℕ, Summable fun k ↦ hsVec ((ξ k : MatFam Y) n) :=
    fun n ↦ Summable.of_norm_bounded (hbsum.mul_right (Real.sqrt (w n)))
      fun k ↦ hnormle k n
  -- the tail majorants
  have htail : ∀ N : ℕ, Summable fun i ↦ ‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N) :=
    fun N ↦ (summable_nat_add_iff N).2 hbsum
  have htailnn : ∀ N : ℕ,
      (0 : ℝ) ≤ ∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N)) :=
    fun N ↦ tsum_nonneg fun i ↦ hbnn (i + N)
  have htailbound : ∀ N n : ℕ,
      ‖∑' i, hsVec ((ξ (i + N) : MatFam Y) n)‖
        ≤ (∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N))) * Real.sqrt (w n) :=
    fun N n ↦ tsum_of_norm_bounded
      ((htail N).hasSum.mul_right (Real.sqrt (w n))) fun i ↦ hnormle (i + N) n
  -- the tail families, mass-bounded with the square of the tail sum
  have htailmem : ∀ N : ℕ,
      (fun n ↦ hsMat (∑' i, hsVec ((ξ (i + N) : MatFam Y) n)))
        ∈ massBounded Y w := fun N ↦
    ⟨(∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N))) ^ 2, fun n ↦
      matMass_hsMat_le _ (hw n) (htailbound N n)⟩
  -- the candidate limit is the tail at `N = 0`
  refine ⟨mkK Y w ω hw ⟨_, htailmem 0⟩, ?_⟩
  have hsplit : ∀ N : ℕ,
      (⟨_, htailmem 0⟩ : massBounded Y w)
        = (∑ k ∈ Finset.range N, ξ k) + ⟨_, htailmem N⟩ := by
    intro N
    have hfam : ∀ n : ℕ,
        hsMat (∑' i, hsVec ((ξ i : MatFam Y) n))
          = (∑ k ∈ Finset.range N, (ξ k : MatFam Y) n)
            + hsMat (∑' i, hsVec ((ξ (i + N) : MatFam Y) n)) := by
      intro n
      rw [← (hsummable n).sum_add_tsum_nat_add N, hsMat_add, hsMat_sum_hsVec]
    refine Subtype.ext (funext fun n ↦ ?_)
    rw [Submodule.coe_add, Pi.add_apply,
      AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    exact hfam n
  have hdiff : ∀ N : ℕ,
      ‖(∑ k ∈ Finset.range N, u k) - mkK Y w ω hw ⟨_, htailmem 0⟩‖
        ≤ ∑' i, (‖u (i + N)‖ + (1 / 2 : ℝ) ^ (i + N)) := by
    intro N
    have hsum : (∑ k ∈ Finset.range N, u k)
        = mkK Y w ω hw (∑ k ∈ Finset.range N, ξ k) := by
      rw [mkK_sum hw (Finset.range N) ξ]
      simp only [hξeq]
    have hval : (∑ k ∈ Finset.range N, u k)
        - mkK Y w ω hw ⟨_, htailmem 0⟩
          = -mkK Y w ω hw ⟨_, htailmem N⟩ := by
      rw [hsum, hsplit N, mkK_add]
      abel
    rw [hval, norm_neg]
    exact norm_mkK_le hw (htailnn N) fun n ↦
      matMass_hsMat_le _ (hw n) (htailbound N n)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun N ↦ norm_nonneg _) hdiff ?_
  exact tendsto_sum_nat_add (fun k ↦ ‖u k‖ + (1 / 2 : ℝ) ^ k)

/-- **KT.05, completed.**  `K_ω` is complete.

With `KOmegaHilbert.kOmegaInnerProductSpace` this makes the manuscript's `K_ω` a
Hilbert space in mathlib's sense, so that the orthogonal complements, orthogonal
projections and spectral theory the printed proof of the Kazhdan transport result
uses on it are all available. -/
instance kOmegaCompleteSpace (hw : ∀ n, 0 ≤ w n) :
    CompleteSpace (KOmega Y w ω hw) :=
  NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
    fun u hu ↦ exists_tendsto_sum_of_summable_norm hw u hu

end Complete

end

end OmegaHilbertComplete
end GroupApproximation
