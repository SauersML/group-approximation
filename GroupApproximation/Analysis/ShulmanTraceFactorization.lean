import GroupApproximation.Analysis.ShulmanTraceNorms
import GroupApproximation.Analysis.TracialMatrixUltraproduct
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The factorization form of a hyperlinear trace, and the Hamel-basis lift

A trace can also be presented as `τ = tr ∘ f` for a `⋆`-homomorphism
`f : A → ∏ M_{kₙ} / ⊕₂ M_{kₙ}`, where `⊕₂ M_{kₙ}` is the ideal of sequences
converging to `0` in the `2`-norm and `tr [(Tₙ)] = limω tr Tₙ`.
`IsFactoredHyperlinearTrace` is that shape, stated against the tracial matrix
quotient of `Analysis/TracialMatrixUltraproduct.lean`, with `tr` its
`ultratrace`.  The quotient is taken along an ultrafilter refining `atTop`,
because that is where the ultratrace of an arbitrary bounded sequence is
defined: at `atTop` alone `limₙ tr(aₙ)` need not exist.

**It is a separate predicate, not a restatement.**  Neither implication is
asserted as an equivalence anywhere, and nothing is taken on anyone's
authority: the analysis below is worked out from the definitions.

## Both directions, and the one clause that is open

*Sequential ⟹ factorized* is `isFactoredHyperlinearTrace_of_model`.  The
assignment `a ↦ [(φₙ(a))]` is a `⋆`-homomorphism because every one of the
three defects vanishes in `‖·‖₂` and is therefore killed by the quotient, and
`tr ∘ it = τ` because the trace clause is an ordinary limit along `atTop`,
hence along any refining ultrafilter.

*Factorized ⟹ sequential*, up to the filter, is
`exists_traceApproximationModel_of_isFactored`.  It does the Hamel-basis lift:
a ℂ-basis of `A`, one choice of preimage per basis vector, extended linearly
to `Φ : A →ₗ[ℂ] ∏ M_{kₙ}` with `mk ∘ Φ = f`.  No continuous section is used
and `Classical.choice` is inside the permitted axiom set.  With
`φₙ a := Φ a n`, **all five clauses hold** — the linearity defect is exactly
`0` rather than asymptotically `0`, the multiplicativity and `⋆` defects lie in
the ideal because the quotient map kills them, and the uniform bound is free
because `Φ` lands in the bounded product.

The limits, however, are along the factorization's own ultrafilter `ω`, while
`IsHyperlinearTrace` reads them along `atTop`.  Four of the five clauses are
indifferent to that: `isHilbertSchmidtNull_mul` and `isHilbertSchmidtNull_star`
are ideal membership, `lift_linear_defect` is an identity, and `bounded`
mentions no filter.  **The trace clause is the only one that is not**, and it
is open here for a reason worth recording rather than retrying:

`tr` on the quotient is an ultralimit, so `tr ∘ f = τ` gives
`limω tr φₙ(a) = τ(a)`.  Choosing a different lift cannot repair this — two
lifts of the same `f` differ by a map into the ideal and `|tr x| ≤ ‖x‖₂`, so
the `atTop` behaviour of `n ↦ tr φₙ(a)` is the same for every lift.  Passing
to a subsequence fixes one `a`, and a diagonal argument fixes countably many;
but `a ↦ tr φₙ(a)` and `τ` are both linear, so the set of `a` that get fixed
is a ℂ-linear subspace, which reaches the span of a countable set and stops.
Crossing from a dense subspace to all of `A` needs `Φ` *continuous*, which a
Hamel lift is exactly not.

So the gap is named to the clause, and it is stated rather than assumed: no
declaration here or downstream pretends to have it.

## Nonempty models

`ModelBoundedSequence` asks for `∀ n, Nonempty (X n)` — the `kₙ ≥ 1` implicit
in writing `M_{kₙ}`, and without it the bounded product is not a unital ring.
It is a hypothesis of the sequential-to-factorized direction rather than a
clause of `TraceApproximationModel`, because a trace that is identically `0`
is modelled by empty matrices and nothing forces `kₙ ≥ 1` from the five
clauses alone.

## Not a bundled `StarAlgHom`, on purpose

The homomorphism is carried as a bare function together with its four
identities rather than as `A →⋆ₐ[ℂ] _`.  No clause of
`TraceApproximationModel` mentions `φₙ(1)`, so nothing in the hypothesis makes
`a ↦ [(φₙ(a))]` unital: it is a *non-unital* `⋆`-homomorphism, and bundling as
a unital one would assert something the hypothesis does not give.
-/

open Filter Matrix
open scoped Matrix.Norms.L2Operator

namespace GroupApproximation
namespace ShulmanTrace

open TracialUltraproduct

/- No proof budget is raised here and none is needed: `TracialMatrixQuotient`
is opaque to instance search and carries its own instances, so no goal about
the quotient unfolds `lp` or rediscovers the `FiniteModel` projections.  The
section-variable linter is off for an unrelated reason: the nonemptiness
instance is a standing hypothesis that many of the coordinatewise steps do not
mention. -/
set_option linter.unusedSectionVars false

noncomputable section

/-! ## Bounded sequences from pointwise bounds -/

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- A pointwise operator-norm-bounded family of matrices, as an element of the
bounded sequence algebra `ℓ∞`. -/
def boundedSeqOfBound (f : ∀ n, Matrix (X n) (X n) ℂ) {C : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ C) : ModelBoundedSequence X :=
  ⟨f, memℓp_infty ⟨C, by
    rintro _ ⟨n, rfl⟩
    exact hf n⟩⟩

omit [∀ n, Nonempty (X n)] in
@[simp] theorem boundedSeqOfBound_apply (f : ∀ n, Matrix (X n) (X n) ℂ) {C : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ C) (n : ℕ) :
    boundedSeqOfBound f hf n = f n :=
  rfl

/-- **The transfer the easy direction runs through.**  Two bounded sequences
whose coordinatewise difference is `‖·‖₂`-null along `atTop` have the same
class in the quotient at any ultrafilter refining `atTop`. -/
theorem mk_eq_mk_of_tendsto {ω : Ultrafilter ℕ} (hω : (ω : Filter ℕ) ≤ atTop)
    {p q : ModelBoundedSequence X}
    (h : Tendsto (fun n ↦ hsNorm (X n) (p n - q n)) atTop (nhds 0)) :
    tracialMatrixQuotientMk X (ω : Filter ℕ) p
      = tracialMatrixQuotientMk X (ω : Filter ℕ) q := by
  have hnull : IsHilbertSchmidtNull X (ω : Filter ℕ) (p - q) := h.mono_left hω
  have hzero : tracialMatrixQuotientMk X (ω : Filter ℕ) (p - q) = 0 :=
    (tracialMatrixQuotientMk_eq_zero_iff X (ω : Filter ℕ) (p - q)).mpr hnull
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Scalars pass through the quotient map. -/
@[simp] theorem smul_tracialMatrixQuotientMk {l : Filter ℕ} (c : ℂ)
    (p : ModelBoundedSequence X) :
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
  /-- The sizes are positive, which is what `M_{kₙ}` means. -/
  [nonempty : ∀ n, Nonempty (space n)]
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

attribute [instance] UltraproductFactorization.nonempty

/-- `τ` factors: it is `tr ∘ f` for a `⋆`-homomorphism into a tracial matrix
quotient. -/
def IsFactoredHyperlinearTrace (τ : A → ℂ) : Prop :=
  Nonempty (UltraproductFactorization τ)

/-! ## Sequential implies factorized -/

/-- The bounded matrix sequence of the models of a fixed element. -/
def modelSeq {τ : A → ℂ}
    (M : TraceApproximationModel atTop (fun Y B ↦ hsNorm Y B) τ)
    [∀ n, Nonempty (M.space n)] {C : A → ℝ}
    (hC : ∀ (a : A) (n : ℕ), ‖M.map n a‖ ≤ C a) (a : A) :
    ModelBoundedSequence M.space :=
  boundedSeqOfBound (fun n ↦ M.map n a) (hC a)

@[simp] theorem modelSeq_apply {τ : A → ℂ}
    (M : TraceApproximationModel atTop (fun Y B ↦ hsNorm Y B) τ)
    [∀ n, Nonempty (M.space n)] {C : A → ℝ}
    (hC : ∀ (a : A) (n : ℕ), ‖M.map n a‖ ≤ C a) (a : A) (n : ℕ) :
    modelSeq M hC a n = M.map n a :=
  rfl

/-- **Sequential implies factorized.**  Each homomorphism identity is the
corresponding defect clause read in the quotient: the defect is `‖·‖₂`-null
along `atTop`, hence along the ultrafilter, hence in the ideal.  The trace
clause is an ordinary limit, so it survives refinement and is pinned by
uniqueness of limits. -/
theorem isFactoredHyperlinearTrace_of_model {τ : A → ℂ}
    (M : TraceApproximationModel atTop (fun Y B ↦ hsNorm Y B) τ)
    (hne : ∀ n, Nonempty (M.space n)) : IsFactoredHyperlinearTrace τ := by
  haveI := hne
  choose C hC using M.bounded
  have hfree : ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ) ≤ atTop :=
    Ultrafilter.of_le _
  refine ⟨{
    space := M.space
    nonempty := hne
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
    rw [ultratrace_mk]
    have hconv : Tendsto (fun n ↦ normTrace (M.space n) (M.map n a)) atTop
        (nhds (τ a)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine (M.tendsto_trace a).congr fun n ↦ ?_
      exact norm_sub_rev _ _
    exact tendsto_nhds_unique (hconv.mono_left hfree)
      (tendsto_seqUltratrace M.space (Ultrafilter.of (atTop : Filter ℕ))
        (modelSeq M hC a))

/-! ## The Hamel-basis lift: factorized implies sequential, up to the filter -/

namespace UltraproductFactorization

variable {τ : A → ℂ}

/-- One preimage in the bounded product for each Hamel basis vector.  The
quotient map is surjective, so this is a choice and nothing more. -/
def liftOnBasis (F : UltraproductFactorization τ) :
    ↥(Module.Basis.ofVectorSpaceIndex ℂ A) → ModelBoundedSequence F.space :=
  fun i ↦ Classical.choose
    (tracialMatrixQuotientMk_surjective F.space (F.ultra : Filter ℕ)
      (F.hom (Module.Basis.ofVectorSpace ℂ A i)))

theorem liftOnBasis_spec (F : UltraproductFactorization τ)
    (i : ↥(Module.Basis.ofVectorSpaceIndex ℂ A)) :
    tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ) (F.liftOnBasis i)
      = F.hom (Module.Basis.ofVectorSpace ℂ A i) :=
  Classical.choose_spec
    (tracialMatrixQuotientMk_surjective F.space (F.ultra : Filter ℕ)
      (F.hom (Module.Basis.ofVectorSpace ℂ A i)))

/-- **The lift.**  Linear by construction — *not* continuous, and it does not
need to be. -/
def lift (F : UltraproductFactorization τ) :
    A →ₗ[ℂ] ModelBoundedSequence F.space :=
  (Module.Basis.ofVectorSpace ℂ A).constr ℂ F.liftOnBasis

/-- `Φ` really is a lift of `f`: two ℂ-linear maps agreeing on a basis. -/
theorem mk_lift (F : UltraproductFactorization τ) (a : A) :
    tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ) (F.lift a)
      = F.hom a := by
  let mkL : ModelBoundedSequence F.space →ₗ[ℂ]
      TracialMatrixQuotient F.space (F.ultra : Filter ℕ) :=
    { toFun := tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ)
      map_add' := fun x y ↦ _root_.map_add _ x y
      map_smul' := fun c p ↦ (smul_tracialMatrixQuotientMk c p).symm }
  let fL : A →ₗ[ℂ] TracialMatrixQuotient F.space (F.ultra : Filter ℕ) :=
    { toFun := F.hom
      map_add' := F.map_add
      map_smul' := F.map_smul }
  have hext : mkL.comp F.lift = fL := by
    refine (Module.Basis.ofVectorSpace ℂ A).ext fun i ↦ ?_
    show tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ)
        (((Module.Basis.ofVectorSpace ℂ A).constr ℂ F.liftOnBasis)
          (Module.Basis.ofVectorSpace ℂ A i))
      = F.hom (Module.Basis.ofVectorSpace ℂ A i)
    rw [Module.Basis.constr_basis]
    exact F.liftOnBasis_spec i
  exact LinearMap.congr_fun hext a

/-- The multiplicativity defect of the lift lies in the ideal, because the
quotient map kills it. -/
theorem isHilbertSchmidtNull_mul (F : UltraproductFactorization τ) (a b : A) :
    IsHilbertSchmidtNull F.space (F.ultra : Filter ℕ)
      (F.lift (a * b) - F.lift a * F.lift b) := by
  have hmk : tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ)
        (F.lift a * F.lift b)
      = tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ) (F.lift a) *
        tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ) (F.lift b) :=
    _root_.map_mul (tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ))
      (F.lift a) (F.lift b)
  refine (tracialMatrixQuotientMk_eq_zero_iff F.space (F.ultra : Filter ℕ)
    _).mp ?_
  rw [_root_.map_sub, hmk, F.mk_lift, F.mk_lift, F.mk_lift, F.map_mul]
  exact sub_self _

/-- The `⋆` defect of the lift lies in the ideal, for the same reason. -/
theorem isHilbertSchmidtNull_star (F : UltraproductFactorization τ) (a : A) :
    IsHilbertSchmidtNull F.space (F.ultra : Filter ℕ)
      (F.lift (star a) - star (F.lift a)) := by
  have hst : tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ)
        (star (F.lift a))
      = star (tracialMatrixQuotientMk F.space (F.ultra : Filter ℕ)
        (F.lift a)) :=
    (tracialMatrixQuotient_star_mk F.space (F.ultra : Filter ℕ) (F.lift a)).symm
  refine (tracialMatrixQuotientMk_eq_zero_iff F.space (F.ultra : Filter ℕ)
    _).mp ?_
  rw [_root_.map_sub, hst, F.mk_lift, F.mk_lift, F.map_star]
  exact sub_self _

/-- **The linearity defect is exactly zero**, not asymptotically zero: this is
what a linear lift buys. -/
theorem lift_linear_defect (F : UltraproductFactorization τ) (c₁ c₂ : ℂ)
    (a b : A) (n : ℕ) :
    F.lift (c₁ • a + c₂ • b) n - c₁ • F.lift a n - c₂ • F.lift b n = 0 := by
  have h : F.lift (c₁ • a + c₂ • b) = c₁ • F.lift a + c₂ • F.lift b := by
    simp only [_root_.map_add, _root_.map_smul]
  rw [h]
  show c₁ • F.lift a n + c₂ • F.lift b n - c₁ • F.lift a n - c₂ • F.lift b n = 0
  abel

/-- The trace of the lift is the ultratrace of the class it lifts. -/
theorem trace_eq_seqUltratrace (F : UltraproductFactorization τ) (a : A) :
    τ a = seqUltratrace F.space F.ultra (F.lift a) := by
  rw [F.trace_eq a, ← F.mk_lift a, ultratrace_mk]

/-- **The Hamel-basis lift as a model.**  All five clauses of the sequential
definition hold for `φₙ a := Φ a n`, with the limits along the factorization's
ultrafilter `ω`.

What separates this from `IsHyperlinearTrace` is the filter and nothing
else. -/
def toModel (F : UltraproductFactorization τ) :
    TraceApproximationModel (F.ultra : Filter ℕ) (fun Y B ↦ hsNorm Y B) τ where
  space := F.space
  map := fun n a ↦ F.lift a n
  tendsto_mul a b := F.isHilbertSchmidtNull_mul a b
  tendsto_linear c₁ c₂ a b := by
    have hz : ∀ n : ℕ, hsNorm (F.space n)
        (F.lift (c₁ • a + c₂ • b) n - c₁ • F.lift a n - c₂ • F.lift b n)
          = 0 := by
      intro n
      rw [F.lift_linear_defect c₁ c₂ a b n]
      exact hsNorm_zero (F.space n)
    refine Tendsto.congr (fun n ↦ (hz n).symm) ?_
    exact tendsto_const_nhds
  tendsto_star a := by
    have hnull : Tendsto (fun n ↦ hsNorm (F.space n)
        ((F.lift (star a) - star (F.lift a)) n)) (F.ultra : Filter ℕ)
          (nhds 0) :=
      F.isHilbertSchmidtNull_star a
    refine hnull.congr fun n ↦ ?_
    show hsNorm (F.space n) (F.lift (star a) n - star (F.lift a n))
      = hsNorm (F.space n) (F.lift (star a) n - (F.lift a n)ᴴ)
    rw [Matrix.star_eq_conjTranspose]
  bounded a := ⟨‖F.lift a‖, fun n ↦
    boundedMatrixSequence_coord_norm_le (fun n ↦ F.space n) (F.lift a) n⟩
  tendsto_trace a := by
    have hconv : Tendsto (fun n ↦ normTrace (F.space n) (F.lift a n))
        (F.ultra : Filter ℕ) (nhds (τ a)) := by
      rw [F.trace_eq_seqUltratrace a]
      exact tendsto_seqUltratrace F.space F.ultra (F.lift a)
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hconv).congr fun n ↦
      norm_sub_rev _ _

end UltraproductFactorization

/-- **The returning direction, up to the filter.**  A factorized trace has
Hilbert–Schmidt matrix models satisfying every clause of the sequential
definition, along an ultrafilter.

`IsHyperlinearTrace` is the same statement along `atTop`, so exactly one step
separates this from the converse of `isFactoredHyperlinearTrace_of_model`:
replacing the ultrafilter by `atTop` in the *trace* clause.  The other four
clauses are filter-uniform.  That step is stated here rather than assumed, and
nothing in this file or downstream of it pretends to have it. -/
theorem exists_traceApproximationModel_of_isFactored {τ : A → ℂ}
    (h : IsFactoredHyperlinearTrace τ) :
    ∃ ω : Ultrafilter ℕ,
      Nonempty (TraceApproximationModel (ω : Filter ℕ)
        (fun Y B ↦ hsNorm Y B) τ) := by
  obtain ⟨F⟩ := h
  exact ⟨F.ultra, ⟨F.toModel⟩⟩

end

end ShulmanTrace
end GroupApproximation
