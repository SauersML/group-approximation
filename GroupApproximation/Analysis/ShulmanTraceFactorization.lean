import GroupApproximation.Analysis.ShulmanTraceNorms
import GroupApproximation.Analysis.TracialMatrixUltraproduct

/-!
# The factorization form of a hyperlinear trace, and the easy direction

A trace can also be presented as `τ = tr ∘ f` for a `⋆`-homomorphism
`f : A → ∏ M_{kₙ} / ⊕₂ M_{kₙ}`, where `⊕₂ M_{kₙ}` is the ideal of sequences
converging to `0` in the `2`-norm and `tr [(Tₙ)] = limω tr Tₙ`.
`IsFactoredHyperlinearTrace` is that shape, stated against the tracial matrix
quotient of `Analysis/TracialMatrixUltraproduct.lean`, with `tr` its
`ultratrace`.  The quotient is taken along an ultrafilter refining `atTop`,
because that is where the ultratrace of an arbitrary bounded sequence is
defined: at `atTop` alone `limₙ tr(aₙ)` need not exist.

**It is a separate predicate, not a restatement.**  This file proves one
implication into it and nothing back, and no declaration anywhere asserts the
two predicates agree.  The literature reports them as equivalent; that report
is not used here, is not an input to any proof below, and the analysis of what
it would cost is worked out from the definitions rather than taken on anyone's
word.

## The direction that is proved

`isFactoredHyperlinearTrace_of_isHyperlinearTrace` : sequential ⟹ factorized.
Given the maps `φₙ`, the assignment `a ↦ [(φₙ(a))]` is a `⋆`-homomorphism
because every one of the three defects vanishes in `‖·‖₂` and is therefore
killed by the quotient, and `tr ∘ it = τ` because the trace clause is an
ordinary limit along `atTop`, hence along any refining ultrafilter.

## The direction that is not, and why it is not one missing lemma

Recovering the `φₙ` from `f` means lifting `f` to `Φ : A → ∏ M_{kₙ}` with
`q ∘ Φ = f` and setting `φₙ a := (Φ a) n`.  There are two obstructions, and
they are not the same size.

*Linearity is the cheap one.*  A ℂ-Hamel basis of `A` and one choice of
preimage per basis vector extend to a genuinely linear `Φ` with `q ∘ Φ = f`.
Then the linearity defect is exactly `0` rather than asymptotically `0`, the
multiplicativity and `⋆` defects land in the ideal because `q` kills them, and
the uniform bound is free because `Φ` lands in the bounded product.  No
section theorem is needed for any of that.

*The trace clause is the real one, and a Hamel lift does not reach it.*  `tr`
on the quotient is an ultralimit, so `tr ∘ f = τ` yields
`limω tr φₙ(a) = τ(a)`, whereas the sequential definition asks for a limit
along `atTop`.  Choosing a different lift cannot help: two lifts differ by a
map into the ideal, and `|tr x| ≤ ‖x‖₂`, so the `atTop` behaviour of
`n ↦ tr φₙ(a)` is the same for every lift of the same `f`.  Passing to a
subsequence fixes one element `a`; a diagonal argument fixes countably many;
and since `a ↦ tr φₙ(a)` and `τ` are both linear, the set of `a` that get
fixed is a ℂ-linear subspace — so this reaches the span of a countable set and
stops there.  Getting from a dense subspace to all of `A` needs `Φ` to be
*continuous*, which is exactly what a Hamel-basis lift is not, and for which
this repository has no substitute.

So the missing direction is not a single extraction step: it needs a lift that
is simultaneously usable and continuous.  Until one exists here, the two
predicates stay separate — an implication in one direction is a formalization,
an `Iff` here would be a claim.

## Not a bundled `StarAlgHom`, on purpose

The homomorphism is carried as a bare function together with its four
identities rather than as `A →⋆ₐ[ℂ] _`.  No clause of
`TraceApproximationModel` mentions `φₙ(1)`, so nothing in the hypothesis makes
`a ↦ [(φₙ(a))]` unital: it is a *non-unital* `⋆`-homomorphism, and bundling as a
unital one would assert something the hypothesis does not give.  Unitality is
recoverable when `τ` is a state, by a faithfulness argument on the quotient
trace; that is not needed here and is not done.
-/

open Filter Matrix
open scoped Matrix.Norms.L2Operator

namespace GroupApproximation
namespace ShulmanTrace

open TracialUltraproduct

noncomputable section

/-! ## Bounded sequences from pointwise bounds -/

/-- A pointwise operator-norm-bounded family of matrices, as an element of the
bounded sequence algebra `ℓ∞`. -/
def boundedSeqOfBound {X : ℕ → FiniteModel} (f : ∀ n, Matrix (X n) (X n) ℂ)
    {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) : ModelBoundedSequence X :=
  ⟨f, memℓp_infty ⟨C, by
    rintro _ ⟨n, rfl⟩
    exact hf n⟩⟩

@[simp] theorem boundedSeqOfBound_apply {X : ℕ → FiniteModel}
    (f : ∀ n, Matrix (X n) (X n) ℂ) {C : ℝ} (hf : ∀ n, ‖f n‖ ≤ C) (n : ℕ) :
    boundedSeqOfBound f hf n = f n :=
  rfl

/-- **The transfer every clause runs through.**  Two bounded sequences whose
coordinatewise difference is `‖·‖₂`-null along `atTop` have the same class in
the quotient at any ultrafilter refining `atTop`. -/
theorem mk_eq_mk_of_tendsto {X : ℕ → FiniteModel} {ω : Ultrafilter ℕ}
    (hω : (ω : Filter ℕ) ≤ atTop) {p q : ModelBoundedSequence X}
    (h : Tendsto (fun n ↦ hsNorm (X n) (p n - q n)) atTop (nhds 0)) :
    tracialMatrixQuotientMk X (ω : Filter ℕ) p
      = tracialMatrixQuotientMk X (ω : Filter ℕ) q := by
  have hnull : IsHilbertSchmidtNull X (ω : Filter ℕ) (p - q) := h.mono_left hω
  have hzero : tracialMatrixQuotientMk X (ω : Filter ℕ) (p - q) = 0 :=
    (tracialMatrixQuotientMk_eq_zero_iff X (ω : Filter ℕ) (p - q)).mpr hnull
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Scalars pass through the quotient map. -/
theorem smul_tracialMatrixQuotientMk {X : ℕ → FiniteModel} {l : Filter ℕ}
    (c : ℂ) (p : ModelBoundedSequence X) :
    c • tracialMatrixQuotientMk X l p = tracialMatrixQuotientMk X l (c • p) :=
  rfl

/-! ## The factorization predicate -/

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- A factorization of `τ` through a tracial matrix quotient: a
`⋆`-homomorphism `f` into `∏ M_{kₙ} / ⊕₂ M_{kₙ}` with `τ = tr ∘ f`.

The homomorphism identities are spelled out rather than bundled; see the
module docstring for why unitality is not among them. -/
structure UltraproductFactorization (τ : A → ℂ) where
  /-- The finite matrix sizes. -/
  space : ℕ → FiniteModel
  /-- The ultrafilter the quotient is taken along. -/
  ultra : Ultrafilter ℕ
  /-- It refines `atTop`, which is what makes the quotient an ultraproduct
  rather than a single matrix algebra. -/
  free : (ultra : Filter ℕ) ≤ atTop
  /-- The homomorphism `f`. -/
  hom : A → TracialMatrixQuotient space (ultra : Filter ℕ)
  /-- `f` is additive. -/
  map_add : ∀ a b : A, hom (a + b) = hom a + hom b
  /-- `f` is complex homogeneous. -/
  map_smul : ∀ (c : ℂ) (a : A), hom (c • a) = c • hom a
  /-- `f` is multiplicative. -/
  map_mul : ∀ a b : A, hom (a * b) = hom a * hom b
  /-- `f` intertwines the adjoints. -/
  map_star : ∀ a : A, hom (star a) = star (hom a)
  /-- `τ = tr ∘ f`. -/
  trace_eq : ∀ a : A, τ a = ultratrace space ultra (hom a)

/-- `τ` factors: it is `tr ∘ f` for a `⋆`-homomorphism into a tracial matrix
quotient.  This is *not* identified with `IsHyperlinearTrace`; only the
implication below is proved. -/
def IsFactoredHyperlinearTrace (τ : A → ℂ) : Prop :=
  Nonempty (UltraproductFactorization τ)

/-- The bounded matrix sequence of the models of a fixed element. -/
def modelSeq {τ : A → ℂ}
    (M : TraceApproximationModel (fun Y B ↦ hsNorm Y B) τ) {C : A → ℝ}
    (hC : ∀ (a : A) (n : ℕ), ‖M.map n a‖ ≤ C a) (a : A) :
    ModelBoundedSequence M.space :=
  boundedSeqOfBound (fun n ↦ M.map n a) (hC a)

@[simp] theorem modelSeq_apply {τ : A → ℂ}
    (M : TraceApproximationModel (fun Y B ↦ hsNorm Y B) τ) {C : A → ℝ}
    (hC : ∀ (a : A) (n : ℕ), ‖M.map n a‖ ≤ C a) (a : A) (n : ℕ) :
    modelSeq M hC a n = M.map n a :=
  rfl

/-! ## Sequential implies factorized -/

/-- **The easy direction.**  A hyperlinear trace in the sequential sense
factors through a tracial matrix quotient.

Each of the four homomorphism identities is the corresponding defect clause of
the sequential definition, read in the quotient: the defect is `‖·‖₂`-null
along `atTop`, hence along the ultrafilter, hence lies in the ideal.  The
trace clause is a limit along `atTop`, so it survives the refinement and is
pinned against the ultratrace by uniqueness of limits.

The converse is not proved, and no result here depends on it; the module
docstring works out what it would cost. -/
theorem isFactoredHyperlinearTrace_of_isHyperlinearTrace {τ : A → ℂ}
    (h : IsHyperlinearTrace τ) : IsFactoredHyperlinearTrace τ := by
  obtain ⟨M⟩ := h
  choose C hC using M.bounded
  have hfree : ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ) ≤ atTop :=
    Ultrafilter.of_le _
  refine ⟨{
    space := M.space
    ultra := Ultrafilter.of (atTop : Filter ℕ)
    free := hfree
    hom := fun a ↦ tracialMatrixQuotientMk M.space
      ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ) (modelSeq M hC a)
    map_add := ?_
    map_smul := ?_
    map_mul := ?_
    map_star := ?_
    trace_eq := ?_ }⟩
  · intro a b
    rw [← map_add (tracialMatrixQuotientMk M.space
      ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ))]
    refine mk_eq_mk_of_tendsto hfree ?_
    have hlin := M.tendsto_linear 1 1 a b
    simp only [one_smul] at hlin
    refine hlin.congr fun n ↦ ?_
    show hsNorm (M.space n) (M.map n (a + b) - M.map n a - M.map n b)
      = hsNorm (M.space n) (M.map n (a + b) - (M.map n a + M.map n b))
    rw [sub_sub]
  · intro c a
    rw [smul_tracialMatrixQuotientMk]
    refine mk_eq_mk_of_tendsto hfree ?_
    have hlin := M.tendsto_linear c 0 a a
    simp only [zero_smul, add_zero, sub_zero] at hlin
    exact hlin
  · intro a b
    rw [← map_mul (tracialMatrixQuotientMk M.space
      ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ))]
    refine mk_eq_mk_of_tendsto hfree ?_
    exact M.tendsto_mul a b
  · intro a
    have hstar : star (tracialMatrixQuotientMk M.space
          ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ) (modelSeq M hC a))
        = tracialMatrixQuotientMk M.space
          ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ)
          (star (modelSeq M hC a)) :=
      tracialMatrixQuotient_star_mk M.space
        ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ) (modelSeq M hC a)
    rw [hstar]
    refine mk_eq_mk_of_tendsto hfree ?_
    refine (M.tendsto_star a).congr fun n ↦ ?_
    show hsNorm (M.space n) (M.map n (star a) - (M.map n a)ᴴ)
      = hsNorm (M.space n) (M.map n (star a) - star (M.map n a))
    rw [Matrix.star_eq_conjTranspose]
  · intro a
    rw [tracialMatrixQuotientMk_apply, ultratrace_mk]
    have hconv : Tendsto (fun n ↦ normTrace (M.space n) (M.map n a)) atTop
        (nhds (τ a)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine (M.tendsto_trace a).congr fun n ↦ ?_
      exact norm_sub_rev _ _
    exact tendsto_nhds_unique (hconv.mono_left hfree)
      (tendsto_seqUltratrace M.space (Ultrafilter.of (atTop : Filter ℕ))
        (modelSeq M hC a))

/-- **Every MF trace factors**, by composing the norm comparison with the
easy direction. -/
theorem isFactoredHyperlinearTrace_of_isMFTrace {τ : A → ℂ}
    (h : IsMFTrace τ) : IsFactoredHyperlinearTrace τ :=
  isFactoredHyperlinearTrace_of_isHyperlinearTrace
    (isHyperlinearTrace_of_isMFTrace h)

end

end ShulmanTrace
end GroupApproximation
