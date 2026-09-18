import GroupApproximation.Analysis.GoldbringHartRoute

/-!
# The trace-kernel quotient of the matrix-sequence corona

Lane TWWSchafhauser-3b (work order WO-TWWCore-3, piece 3b).  This file builds the
first object in Schafhauser's proof of the Tikuisis--White--Winter theorem
(C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. 759 (2020), §2--3; see also Brown--Ozawa, Ch. 6).

Fix nonempty finite models `X n` and a free ultrafilter `ω ≤ cofinite`.  The
objects in the repository's corona formalism are:

* `ℓ∞(M_{X n})` is `BoundedMatrixSequence (fun n => X n)`, which is the same as
  `TracialUltraproduct.ModelBoundedSequence X`.
* The norm corona `Q_ω = ℓ∞(M_{X n}) / c₀(M_{X n})` is
  `NormMatrixCStarCorona (fun n => X n)`, with quotient map
  `normMatrixCStarCoronaMk`.  This is the corona in which
  `Quasidiagonal.CoronaModel` and `isQuasidiagonalTrace_of_hasCoronaModel`
  state multiplicativity.
* The tracial ultraproduct `Q^ω = ℓ∞(M_{X n}) / J₂,ω` quotients by the sequences
  that are null in the normalized Hilbert--Schmidt norm along `ω`.  It is
  `TracialUltraproduct.TracialMatrixQuotient X ω`, with its faithful ultratrace
  `tr_ω`.

`traceKernelQuotient X ω hω : Q_ω →⋆ₐ Q^ω` is the canonical quotient map.  It is
well defined because operator-norm null implies Hilbert--Schmidt null, which
`TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient` proves.
`traceKernelIdeal X ω hω` is its kernel, the trace-kernel ideal `J` of
Schafhauser's extension `0 → J → Q_ω → Q^ω → 0`.

Proved here:

* `traceKernelQuotient_mk`: the map on classes of sequences.
* `traceKernelQuotient_comp_quotient`: `π ∘ (ℓ∞ → Q_ω) = (ℓ∞ → Q^ω)`.
* `traceKernelQuotient_surjective`.
* `mk_mem_traceKernelIdeal_iff`: a class lies in `J` exactly when a representative
  is `‖·‖₂`-null along `ω`.
* `ultratrace_traceKernelQuotient_mk`: `tr_ω (π [x]) = lim_ω tr_{X n}(x n)`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)

/-- **The trace-kernel quotient `Q_ω → Q^ω`** (Schafhauser 2020, §2).  It maps the
cofinite norm-matrix corona onto the tracial matrix ultraproduct along `ω`. -/
abbrev traceKernelQuotient :
    NormMatrixCStarCorona (fun n => X n) →⋆ₐ[ℂ]
      TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ) :=
  TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient X ω hω

/-- The trace-kernel quotient on the class of a bounded sequence. -/
theorem traceKernelQuotient_mk (a : TracialUltraproduct.ModelBoundedSequence X) :
    traceKernelQuotient X ω hω (normMatrixCStarCoronaMk (fun n => X n) a)
      = TracialUltraproduct.tracialMatrixQuotientMk X (ω : Filter ℕ) a :=
  TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient_mk X ω hω a

/-- The two quotient maps out of `ℓ∞(M_{X n})` are compatible. -/
theorem traceKernelQuotient_comp_quotient :
    (traceKernelQuotient X ω hω).comp (normMatrixCStarCoronaQuotient (fun n => X n))
      = TracialUltraproduct.tracialMatrixQuotientQuotient X (ω : Filter ℕ) :=
  StarAlgHom.ext fun a => traceKernelQuotient_mk X ω hω a

/-- The trace-kernel quotient is onto. -/
theorem traceKernelQuotient_surjective :
    Function.Surjective (traceKernelQuotient X ω hω) := by
  intro y
  obtain ⟨a, rfl⟩ :=
    TracialUltraproduct.tracialMatrixQuotientMk_surjective X (ω : Filter ℕ) y
  exact ⟨normMatrixCStarCoronaMk (fun n => X n) a, traceKernelQuotient_mk X ω hω a⟩

/-- **The trace-kernel ideal `J ⊆ Q_ω`** (Schafhauser 2020, §2), defined as the
kernel of `traceKernelQuotient`. -/
def traceKernelIdeal : Ideal (NormMatrixCStarCorona (fun n => X n)) :=
  RingHom.ker (traceKernelQuotient X ω hω)

theorem mem_traceKernelIdeal_iff (x : NormMatrixCStarCorona (fun n => X n)) :
    x ∈ traceKernelIdeal X ω hω ↔ traceKernelQuotient X ω hω x = 0 :=
  RingHom.mem_ker

/-- **Membership in the trace kernel.**  The class of `a` lies in `J` exactly when
`‖a n‖₂ → 0` along `ω`. -/
theorem mk_mem_traceKernelIdeal_iff (a : TracialUltraproduct.ModelBoundedSequence X) :
    normMatrixCStarCoronaMk (fun n => X n) a ∈ traceKernelIdeal X ω hω
      ↔ TracialUltraproduct.IsHilbertSchmidtNull X (ω : Filter ℕ) a := by
  rw [mem_traceKernelIdeal_iff, traceKernelQuotient_mk]
  exact TracialUltraproduct.tracialMatrixQuotientMk_eq_zero_iff X (ω : Filter ℕ) a

/-- The ultratrace of the trace-kernel image of a class is the `ω`-limit of the
normalized traces of any representative. -/
theorem ultratrace_traceKernelQuotient_mk
    (a : TracialUltraproduct.ModelBoundedSequence X) :
    TracialUltraproduct.ultratrace X ω
        (traceKernelQuotient X ω hω (normMatrixCStarCoronaMk (fun n => X n) a))
      = TracialUltraproduct.seqUltratrace X ω a := by
  rw [traceKernelQuotient_mk, TracialUltraproduct.ultratrace_mk]

end

end GroupApproximation.Full.TWWSchafhauser
