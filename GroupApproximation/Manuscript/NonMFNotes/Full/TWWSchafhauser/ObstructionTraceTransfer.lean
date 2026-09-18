import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingTraceKernel

/-!
# Trace transfer for the lifting step of Schafhauser's argument

Lane `TWWSchafhauser-3d1` (work order `WO-TWWSchafhauser-3d-1`).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*,
J. reine angew. Math. **759** (2020), 291--304, §4--5.

Schafhauser's lifting step starts from a trace-preserving `θ : A → Q^ω` and ends with
a unital `⋆`-homomorphism `ψ` into the norm corona.  Up to unitary equivalence, `ψ`
lifts `θ` through the trace-kernel quotient `Q_ω → Q^ω`.  Its trace condition follows
from two elementary facts, proved here.

* **Corona maps.**
  - `filterCoronaToTracialQuotient X l`: the norm corona `ℓ∞(M_{X n}) / c_l` along a
    filter `l` maps onto the tracial quotient `Q^l`.  An operator-norm-null sequence is
    Hilbert--Schmidt null along the same filter.
  - `normCoronaToFilterCorona X l hl`: for `l ≤ cofinite` the cofinite corona descends
    to the `l`-corona.
  - `filterCoronaToTracialQuotient_comp_normCoronaToFilterCorona`: the composite is the
    3b trace-kernel quotient `traceKernelQuotient`.
* **Traces.**
  - `tendsto_norm_sub_normTrace_of_ultratrace_eq`: if the limit trace of the class of
    `a` is `c`, then `tr_{X n}(a n) → c` along `ω`.
  - `ultratrace_conj`, `ultratrace_traceKernelQuotient_conj`: conjugation by an
    isometry `v` (`star v * v = 1`) does not change the limit trace, in `Q^ω` and
    through the corona.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Norm-null sequences are trace-null -/

/-- **Operator-norm nullity along `l` gives Hilbert--Schmidt nullity along `l`**,
because `‖x‖₂ ≤ ‖x‖` (Schafhauser 2020, §2: `c_ω ⊆ J_ω`). -/
theorem isHilbertSchmidtNull_of_isNullMatrixSequence (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (l : Filter ℕ) (a : TracialUltraproduct.ModelBoundedSequence X)
    (ha : IsNullMatrixSequence (fun n ↦ (X n).carrier) l a) :
    TracialUltraproduct.IsHilbertSchmidtNull X l a :=
  squeeze_zero' (Eventually.of_forall fun n ↦ hsNorm_nonneg (X n) (a n))
    (Eventually.of_forall fun n ↦ PrelimNotation.hsNorm_le_l2_opNorm (X n) (a n)) ha

/-! ## The corona maps -/

/-- **The trace-kernel quotient at a filter**, `ℓ∞(M_{X n}) / c_l → Q^l`
(Schafhauser 2020, §2, the quotient `Q_ω → Q^ω` at `l = ω`). -/
def filterCoronaToTracialQuotient (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (l : Filter ℕ) :
    FilterMatrixCStarCorona (fun n ↦ (X n).carrier) l →⋆ₐ[ℂ]
      TracialUltraproduct.TracialMatrixQuotient X l :=
  filterMatrixCStarCoronaLift (fun n ↦ (X n).carrier) l
    (TracialUltraproduct.tracialMatrixQuotientQuotient X l)
    (fun a ha ↦ (TracialUltraproduct.tracialMatrixQuotientMk_eq_zero_iff X l a).mpr
      (isHilbertSchmidtNull_of_isNullMatrixSequence X l a ha))

@[simp] theorem filterCoronaToTracialQuotient_mk (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (l : Filter ℕ) (a : TracialUltraproduct.ModelBoundedSequence X) :
    filterCoronaToTracialQuotient X l (filterMatrixCStarCoronaMk (fun n ↦ (X n).carrier) l a)
      = TracialUltraproduct.tracialMatrixQuotientMk X l a :=
  rfl

/-- **Descent from the cofinite corona to the corona at a finer filter.**  A
sequence null along `cofinite` is null along every `l ≤ cofinite`. -/
def normCoronaToFilterCorona (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (l : Filter ℕ) (hl : l ≤ cofinite) :
    NormMatrixCStarCorona (fun n ↦ (X n).carrier) →⋆ₐ[ℂ]
      FilterMatrixCStarCorona (fun n ↦ (X n).carrier) l := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaStarLift (fun n ↦ (X n).carrier) cofinite
    (filterMatrixCStarCoronaQuotient (fun n ↦ (X n).carrier) l)
    (fun a ha ↦ (filterMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ (X n).carrier) l a).mpr
      (ha.mono_left hl))

@[simp] theorem normCoronaToFilterCorona_mk (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (l : Filter ℕ) (hl : l ≤ cofinite) (a : TracialUltraproduct.ModelBoundedSequence X) :
    normCoronaToFilterCorona X l hl (normMatrixCStarCoronaMk (fun n ↦ (X n).carrier) a)
      = filterMatrixCStarCoronaMk (fun n ↦ (X n).carrier) l a :=
  rfl

/-- The descent followed by the trace-kernel quotient at `ω` is the 3b trace-kernel
quotient `traceKernelQuotient X ω hω`. -/
theorem filterCoronaToTracialQuotient_comp_normCoronaToFilterCorona (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (x : NormMatrixCStarCorona (fun n ↦ (X n).carrier)) :
    filterCoronaToTracialQuotient X (ω : Filter ℕ) (normCoronaToFilterCorona X ω hω x)
      = traceKernelQuotient X ω hω x := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ (X n).carrier) x
  rw [normCoronaToFilterCorona_mk, filterCoronaToTracialQuotient_mk, traceKernelQuotient_mk]

/-! ## Traces along `ω` -/

/-- The normalized traces of a bounded sequence converge, along `ω`, to its limit
trace. -/
theorem tendsto_norm_sub_normTrace (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (a : TracialUltraproduct.ModelBoundedSequence X) :
    Tendsto (fun n ↦ ‖TracialUltraproduct.seqUltratrace X ω a - normTrace (X n) (a n)‖)
      (ω : Filter ℕ) (nhds 0) := by
  have hconst : Tendsto (fun _ : ℕ ↦ TracialUltraproduct.seqUltratrace X ω a)
      (ω : Filter ℕ) (nhds (TracialUltraproduct.seqUltratrace X ω a)) :=
    tendsto_const_nhds
  have hsub := (hconst.sub (TracialUltraproduct.tendsto_seqUltratrace X ω a)).norm
  rw [sub_self, norm_zero] at hsub
  exact hsub

/-- **Trace convergence from the limit trace of the class.**  If `[a] = x` in the
`ω`-corona and `tr_ω (π x) = c`, then `‖c - tr_{X n}(a n)‖ → 0` along `ω`
(Schafhauser 2020, §5, the trace condition of the lift). -/
theorem tendsto_norm_sub_normTrace_of_ultratrace_eq (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ) {c : ℂ}
    {x : FilterMatrixCStarCorona (fun n ↦ (X n).carrier) (ω : Filter ℕ)}
    (a : TracialUltraproduct.ModelBoundedSequence X)
    (ha : filterMatrixCStarCoronaMk (fun n ↦ (X n).carrier) (ω : Filter ℕ) a = x)
    (hc : TracialUltraproduct.ultratrace X ω (filterCoronaToTracialQuotient X ω x) = c) :
    Tendsto (fun n ↦ ‖c - normTrace (X n) (a n)‖) (ω : Filter ℕ) (nhds 0) := by
  subst ha
  rw [filterCoronaToTracialQuotient_mk, TracialUltraproduct.ultratrace_mk] at hc
  subst hc
  exact tendsto_norm_sub_normTrace X ω a

/-! ## Conjugation does not change the limit trace -/

/-- **The limit trace is invariant under conjugation by an isometry** of `Q^ω`
(Schafhauser 2020, §5: unitary equivalence preserves the induced trace). -/
theorem ultratrace_conj (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
    {v : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)} (hv : star v * v = 1)
    (y : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)) :
    TracialUltraproduct.ultratrace X ω (v * y * star v) = TracialUltraproduct.ultratrace X ω y := by
  rw [mul_assoc, TracialUltraproduct.ultratrace_mul_comm X ω v (y * star v), mul_assoc, hv,
    mul_one]

/-- **Conjugation in the corona does not change the limit trace.**  For `u` in the
`ω`-corona with `star u * u = 1`, `tr_ω (π (u x u⋆)) = tr_ω (π x)`. -/
theorem ultratrace_filterCoronaToTracialQuotient_conj (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
    {u : FilterMatrixCStarCorona (fun n ↦ (X n).carrier) (ω : Filter ℕ)} (hu : star u * u = 1)
    (x : FilterMatrixCStarCorona (fun n ↦ (X n).carrier) (ω : Filter ℕ)) :
    TracialUltraproduct.ultratrace X ω (filterCoronaToTracialQuotient X ω (u * x * star u))
      = TracialUltraproduct.ultratrace X ω (filterCoronaToTracialQuotient X ω x) := by
  have hv : star (filterCoronaToTracialQuotient X ω u) * filterCoronaToTracialQuotient X ω u
      = 1 := by
    rw [← map_star, ← map_mul, hu, map_one]
  rw [map_mul, map_mul, map_star]
  exact ultratrace_conj X ω hv (filterCoronaToTracialQuotient X ω x)

/-- **Trace transfer through the 3b trace-kernel quotient.**  Suppose `π (ψ a) = v θ(a) v⋆`
in `Q^ω`, where `star v * v = 1`, and `θ` preserves `τ`.  Then `ψ` induces `τ`
(Schafhauser 2020, §5). -/
theorem ultratrace_traceKernelQuotient_conj (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    {v : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)} (hv : star v * v = 1)
    {x : NormMatrixCStarCorona (fun n ↦ (X n).carrier)}
    {y : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)} {c : ℂ}
    (hxy : traceKernelQuotient X ω hω x = v * y * star v)
    (hy : TracialUltraproduct.ultratrace X ω y = c) :
    TracialUltraproduct.ultratrace X ω
        (filterCoronaToTracialQuotient X (ω : Filter ℕ) (normCoronaToFilterCorona X ω hω x))
      = c := by
  rw [filterCoronaToTracialQuotient_comp_normCoronaToFilterCorona, hxy, ultratrace_conj X ω hv,
    hy]

end

end GroupApproximation.Full.TWWSchafhauser
