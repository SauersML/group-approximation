import GroupApproximation.Sofic.SoficPermutationTrace
import GroupApproximation.Analysis.ShulmanTraceFromRepresentation

/-!
# The canonical trace of a sofic group is hyperlinear: the middle of the bridge

`Sofic/SoficPermutationTrace.lean` ends at the generator trace values of a
sofic approximation, along ordinary `atTop`.  The C-star structure of the
`atTop` tracial matrix quotient is being proved elsewhere and is not assumed
here.  This file is everything in between, and it is complete: no declaration
below is conditional on the missing instance.

## Contents

* **The sofic unitary representation.**  `soficUnitarySeq` places the
  permutation-matrix models of a sofic approximation inside the bounded
  product; each coordinate is exactly unitary, so the uniform bound is `1`.
  The multiplicativity and identity defects are Hamming defects doubled
  (`permMatrix_hsDistSq`), hence `‖·‖₂`-null along `atTop`, hence ideal
  membership; `soficUnitaryHom` is the resulting genuine group homomorphism
  into the unitary group of the `atTop` tracial matrix quotient.

* **Span transport.**  `exists_rep_tendsto_of_span`: representatives with
  convergent coordinate traces propagate from a set to its ℂ-linear span.
  The representatives are *added by hand* — `p + q` for `x + y` — because the
  downstream representative choice `qrep` is deliberately non-linear, so
  nothing about it can be inducted on directly.

* **The `ε/3` crossing.**  `tendsto_norm_trace_qrep`: for a contractive
  additive-homogeneous `Φ` into the `atTop` quotient and a continuous `τ`
  whose trace clause holds on a dense-spanning set, the trace clause holds for
  the `qrep` model on *every* element.  The `+1` slack in `qrep_norm_lt` is
  harmless: at tolerance `δ` the comparison uses a **fresh** representative of
  `Φ (a - b)` within `δ` of the quotient-norm infimum, so the additive slack
  scales with the tolerance instead of being fixed.  This is the step the
  Hamel-basis lift of `ShulmanTraceFactorization` provably cannot make — a
  linear lift has no norm control — and the reason the sequential trace clause
  is available here at all.

* **The assembly.**  `isHyperlinearTrace_canonicalMaximalTrace_of_soficRepresentation`:
  given *any* ⋆-homomorphism `π` out of `C*(G)` that restricts to the sofic
  unitary classes on the generators and is contractive, the canonical trace of
  `C*(G)` is hyperlinear — in Shulman's sequential sense, along `atTop`, with
  no ultrafilter anywhere.  The universal property of `C*(G)` will supply `π`
  the moment the quotient's `CStarAlgebra` instance exists; its two
  hypotheses (`hπgen`, `hπnorm`) are exactly what
  `maximalGroupCStar_existsUnique_lift` and ⋆-homomorphism contractivity
  produce.  Nothing else will be missing.

## Why the trace clause crosses, in one paragraph

For `a ∈ C*(G)` and tolerance `ε`, pick `b` in the span of the canonical
unitaries with `‖a - b‖` small, a representative `p` of `Φ b` with convergent
traces (span transport from the permutation models), and a representative `r`
of `Φ (a - b)` of norm `< ‖a - b‖ + δ` (contractivity).  Then
`qrep Φ a - p - r` represents `0`, so its coordinate `‖·‖₂`-norms vanish; and
`|tr x| ≤ ‖x‖₂` on the null part while `|tr (r n)| ≤ ‖r n‖ ≤ ‖r‖` on the
fresh representative.  So the coordinate traces of `qrep Φ a` and of `p`
eventually differ by at most `3δ`, and `τ` moves by at most `‖τ‖·δ` from `a`
to `b`.  Sum: `(‖τ‖ + 4)·δ`, and `δ` was chosen as `ε / (‖τ‖ + 4)`.
-/

namespace GroupApproximation
namespace ShulmanTrace

open Filter Matrix TracialUltraproduct SoficPermutationTrace
open scoped Matrix.Norms.L2Operator

/- Above the budget of `TracialMatrixUltraproduct` itself: from a foreign file
every use of `*` on the quotient re-runs the search through
`Ideal.Quotient.ring` and the `lp.inftyRing` chain, which rediscovers each
model's `Fintype`/`DecidableEq` through the `FiniteModel` projections.  The
first build of this file timed out at 1,000,000 exactly there
(`soficUnitaryHom`, and `map_mul π` in the assembly). -/
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

/-! ## Coordinate probes

The bounded product is `lp` at `∞`, whose algebra operations are pointwise by
definition.  Concentrating the definitional unfoldings here keeps every proof
below free of `lp` internals. -/

section CoordinateProbes

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

omit [∀ n, Nonempty (X n)] in
@[simp] theorem modelSeq_add_apply (p q : ModelBoundedSequence X) (n : ℕ) :
    (p + q) n = p n + q n := rfl

omit [∀ n, Nonempty (X n)] in
@[simp] theorem modelSeq_sub_apply (p q : ModelBoundedSequence X) (n : ℕ) :
    (p - q) n = p n - q n := rfl

omit [∀ n, Nonempty (X n)] in
@[simp] theorem modelSeq_mul_apply (p q : ModelBoundedSequence X) (n : ℕ) :
    (p * q) n = p n * q n := rfl

@[simp] theorem modelSeq_smul_apply (c : ℂ) (p : ModelBoundedSequence X)
    (n : ℕ) : (c • p) n = c • p n := rfl

@[simp] theorem modelSeq_one_apply (n : ℕ) :
    (1 : ModelBoundedSequence X) n = 1 := rfl

omit [∀ n, Nonempty (X n)] in
@[simp] theorem modelSeq_zero_apply (n : ℕ) :
    (0 : ModelBoundedSequence X) n = 0 := rfl

omit [∀ n, Nonempty (X n)] in
@[simp] theorem modelSeq_star_apply (p : ModelBoundedSequence X) (n : ℕ) :
    (star p) n = star (p n) := by
  simp [lp.star_apply]

omit [∀ n, Nonempty (X n)] in
/-- A sequence vanishing in every coordinate is `‖·‖₂`-null along any filter. -/
theorem isHilbertSchmidtNull_of_forall_eq_zero {l : Filter ℕ}
    {a : ModelBoundedSequence X} (h : ∀ n, a n = 0) :
    IsHilbertSchmidtNull X l a := by
  show Tendsto (fun n ↦ hsNorm (X n) (a n)) l (nhds 0)
  refine tendsto_const_nhds.congr fun n ↦ ?_
  rw [h n, hsNorm_zero]

end CoordinateProbes

/-! ## A. The sofic unitary representation in the `atTop` tracial quotient -/

section SoficRepresentation

variable {G : Type*} [Group G] (S : SoficApproximation G)
variable [∀ n, Nonempty (S.model n)]

/-- Each permutation-matrix model has operator norm exactly `1`. -/
theorem norm_modelUnitary (n : ℕ) (g : G) : ‖modelUnitary S n g‖ = 1 := by
  haveI : Nontrivial (Matrix (S.model n) (S.model n) ℂ) := by
    refine nontrivial_of_ne 1 0 fun h ↦ ?_
    have h1 : ‖(1 : Matrix (S.model n) (S.model n) ℂ)‖ = 1 := norm_one
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  exact CStarRing.norm_of_mem_unitary (modelUnitary_mem_unitaryGroup S n g)

/-- The permutation-matrix models of one group element, as an element of the
bounded product. -/
def soficUnitarySeq (g : G) : ModelBoundedSequence (fun n ↦ S.model n) :=
  boundedSeqOfBound (fun n ↦ modelUnitary S n g)
    (fun n ↦ le_of_eq (norm_modelUnitary S n g))

@[simp] theorem soficUnitarySeq_apply (g : G) (n : ℕ) :
    soficUnitarySeq S g n = modelUnitary S n g := rfl

omit [∀ n, Nonempty (S.model n)] in
/-- The Hamming multiplicativity defect of the approximation, as an ordinary
limit. -/
theorem tendsto_hamming_mul (g h : G) :
    Tendsto (fun n ↦ hammingDistance (S.model n)
      (S.map n (g * h)) (S.map n g * S.map n h)) atTop (nhds 0) := by
  refine tendsto_zero_of_forall_eventually_lt
    (fun n ↦ hammingDistance_nonnegative _ _ _) ?_
  intro ε hε
  obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h ε hε
  exact Filter.eventually_atTop.mpr ⟨N, hN⟩

omit [∀ n, Nonempty (S.model n)] in
/-- The Hamming distance of the identity model to the identity, as an ordinary
limit. -/
theorem tendsto_hamming_one :
    Tendsto (fun n ↦ hammingDistance (S.model n) (S.map n 1) 1) atTop
      (nhds 0) := by
  refine tendsto_zero_of_forall_eventually_lt
    (fun n ↦ hammingDistance_nonnegative _ _ _) ?_
  intro ε hε
  obtain ⟨N, hN⟩ := S.map_one_close ε hε
  exact Filter.eventually_atTop.mpr ⟨N, hN⟩

/-- **The multiplicativity defect is `‖·‖₂`-null along `atTop`.**  The passage
to matrices is a genuine homomorphism (`permMatrix` of the inverse), so the
whole defect is the Hamming defect, doubled. -/
theorem isHilbertSchmidtNull_soficUnitarySeq_mul (g h : G) :
    IsHilbertSchmidtNull (fun n ↦ S.model n) atTop
      (soficUnitarySeq S (g * h) - soficUnitarySeq S g * soficUnitarySeq S h)
    := by
  rw [isHilbertSchmidtNull_iff_sq]
  have hkey : ∀ n, hsNormSq (S.model n)
      ((soficUnitarySeq S (g * h)
        - soficUnitarySeq S g * soficUnitarySeq S h) n)
      = 2 * hammingDistance (S.model n)
          (S.map n (g * h)) (S.map n g * S.map n h) := by
    intro n
    have hprod : modelUnitary S n g * modelUnitary S n h
        = ((S.map n g * S.map n h)⁻¹).permMatrix ℂ := by
      show ((S.map n g)⁻¹).permMatrix ℂ * ((S.map n h)⁻¹).permMatrix ℂ = _
      rw [_root_.mul_inv_rev, Matrix.permMatrix_mul]
    have hcoord : (soficUnitarySeq S (g * h)
          - soficUnitarySeq S g * soficUnitarySeq S h) n
        = ((S.map n (g * h))⁻¹).permMatrix ℂ
          - ((S.map n g * S.map n h)⁻¹).permMatrix ℂ := by
      rw [modelSeq_sub_apply, modelSeq_mul_apply, soficUnitarySeq_apply,
        soficUnitarySeq_apply, soficUnitarySeq_apply, hprod]
      rfl
    rw [hcoord]
    have hdist : hsNormSq (S.model n)
        (((S.map n (g * h))⁻¹).permMatrix ℂ
          - ((S.map n g * S.map n h)⁻¹).permMatrix ℂ)
        = hsDistSq (S.model n) (((S.map n (g * h))⁻¹).permMatrix ℂ)
            (((S.map n g * S.map n h)⁻¹).permMatrix ℂ) := rfl
    rw [hdist, permMatrix_hsDistSq, hammingDistance_inv]
  have h2 : Tendsto (fun n ↦ 2 * hammingDistance (S.model n)
      (S.map n (g * h)) (S.map n g * S.map n h)) atTop (nhds 0) := by
    simpa using (tendsto_hamming_mul S g h).const_mul (2 : ℝ)
  exact h2.congr fun n ↦ (hkey n).symm

/-- **The identity defect is `‖·‖₂`-null along `atTop`.**  A sofic
approximation only satisfies `σₙ(1) ≈ 1`, so this is a limit, not an
equality. -/
theorem isHilbertSchmidtNull_soficUnitarySeq_one :
    IsHilbertSchmidtNull (fun n ↦ S.model n) atTop
      (soficUnitarySeq S 1 - 1) := by
  rw [isHilbertSchmidtNull_iff_sq]
  have hkey : ∀ n, hsNormSq (S.model n) ((soficUnitarySeq S 1 - 1) n)
      = 2 * hammingDistance (S.model n) (S.map n 1) 1 := by
    intro n
    have hone : (1 : Matrix (S.model n) (S.model n) ℂ)
        = ((1 : Equiv.Perm (S.model n))⁻¹).permMatrix ℂ := by
      rw [inv_one, Matrix.permMatrix_one]
    have hcoord : (soficUnitarySeq S 1 - 1) n
        = ((S.map n 1)⁻¹).permMatrix ℂ
          - ((1 : Equiv.Perm (S.model n))⁻¹).permMatrix ℂ := by
      rw [modelSeq_sub_apply, soficUnitarySeq_apply, modelSeq_one_apply, hone]
      rfl
    rw [hcoord]
    have hdist : hsNormSq (S.model n)
        (((S.map n 1)⁻¹).permMatrix ℂ
          - ((1 : Equiv.Perm (S.model n))⁻¹).permMatrix ℂ)
        = hsDistSq (S.model n) (((S.map n 1)⁻¹).permMatrix ℂ)
            (((1 : Equiv.Perm (S.model n))⁻¹).permMatrix ℂ) := rfl
    rw [hdist, permMatrix_hsDistSq, hammingDistance_inv]
  have h2 : Tendsto (fun n ↦ 2 * hammingDistance (S.model n) (S.map n 1) 1)
      atTop (nhds 0) := by
    simpa using (tendsto_hamming_one S).const_mul (2 : ℝ)
  exact h2.congr fun n ↦ (hkey n).symm

/-- Two bounded sequences whose difference is null have the same class. -/
theorem mk_eq_mk_of_isHilbertSchmidtNull {X : ℕ → FiniteModel}
    [∀ n, Nonempty (X n)] {l : Filter ℕ} {p q : ModelBoundedSequence X}
    (h : IsHilbertSchmidtNull X l (p - q)) :
    tracialMatrixQuotientMk X l p = tracialMatrixQuotientMk X l q := by
  have h0 : tracialMatrixQuotientMk X l (p - q) = 0 :=
    (tracialMatrixQuotientMk_eq_zero_iff X l (p - q)).mpr h
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

/-- The class of a sofic unitary sequence is unitary: each coordinate is
exactly unitary, so both defects vanish identically. -/
theorem mk_soficUnitarySeq_mem_unitary (g : G) :
    tracialMatrixQuotientMk (fun n ↦ S.model n) atTop (soficUnitarySeq S g)
      ∈ unitary (TracialMatrixQuotient (fun n ↦ S.model n) atTop) := by
  have hstar : star (tracialMatrixQuotientMk (fun n ↦ S.model n) atTop
        (soficUnitarySeq S g))
      = tracialMatrixQuotientMk (fun n ↦ S.model n) atTop
        (star (soficUnitarySeq S g)) :=
    tracialMatrixQuotient_star_mk (fun n ↦ S.model n) atTop
      (soficUnitarySeq S g)
  rw [Unitary.mem_iff, hstar, ← map_mul, ← map_mul]
  constructor
  · have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) atTop
        (star (soficUnitarySeq S g) * soficUnitarySeq S g - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply,
        modelSeq_one_apply, soficUnitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff'.mp
        (modelUnitary_mem_unitaryGroup S n g)
      rw [hu, sub_self]
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := atTop) hnull
    rw [this, map_one]
  · have hnull : IsHilbertSchmidtNull (fun n ↦ S.model n) atTop
        (soficUnitarySeq S g * star (soficUnitarySeq S g) - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply,
        modelSeq_one_apply, soficUnitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff.mp
        (modelUnitary_mem_unitaryGroup S n g)
      rw [hu, sub_self]
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := atTop) hnull
    rw [this, map_one]

/-- **The sofic unitary representation.**  The permutation models become a
genuine group homomorphism into the unitary group of the `atTop` tracial
matrix quotient: the identity and multiplicativity defects lie in the ideal,
which forgets them. -/
def soficUnitaryHom :
    G →* unitary (TracialMatrixQuotient (fun n ↦ S.model n) atTop) where
  toFun g := ⟨tracialMatrixQuotientMk (fun n ↦ S.model n) atTop
      (soficUnitarySeq S g), mk_soficUnitarySeq_mem_unitary S g⟩
  map_one' := by
    apply Subtype.ext
    show tracialMatrixQuotientMk (fun n ↦ S.model n) atTop
        (soficUnitarySeq S 1) = 1
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := atTop) (isHilbertSchmidtNull_soficUnitarySeq_one S)
    rw [this, map_one]
  map_mul' g h := by
    apply Subtype.ext
    show tracialMatrixQuotientMk (fun n ↦ S.model n) atTop
        (soficUnitarySeq S (g * h))
      = tracialMatrixQuotientMk (fun n ↦ S.model n) atTop (soficUnitarySeq S g)
        * tracialMatrixQuotientMk (fun n ↦ S.model n) atTop
          (soficUnitarySeq S h)
    rw [← map_mul]
    exact mk_eq_mk_of_isHilbertSchmidtNull (X := fun n ↦ S.model n)
      (l := atTop) (isHilbertSchmidtNull_soficUnitarySeq_mul S g h)

@[simp] theorem soficUnitaryHom_apply_coe (g : G) :
    ((soficUnitaryHom S g : unitary
        (TracialMatrixQuotient (fun n ↦ S.model n) atTop))
      : TracialMatrixQuotient (fun n ↦ S.model n) atTop)
    = tracialMatrixQuotientMk (fun n ↦ S.model n) atTop (soficUnitarySeq S g)
    := rfl

end SoficRepresentation

/-! ## B. Span transport and the `ε/3` crossing -/

section Crossing

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]

/-- Additive homogeneous maps subtract. -/
private theorem phi_sub (Φ : A → TracialMatrixQuotient X atTop)
    (hadd : ∀ a b : A, Φ (a + b) = Φ a + Φ b)
    (hsmul : ∀ (c : ℂ) (a : A), Φ (c • a) = c • Φ a) (a b : A) :
    Φ (a - b) = Φ a - Φ b := by
  have hneg : Φ (-b) = -Φ b := by
    have h := hsmul (-1 : ℂ) b
    rw [neg_one_smul] at h
    rw [h, neg_one_smul]
  rw [sub_eq_add_neg, hadd, hneg, sub_eq_add_neg]

private theorem phi_zero (Φ : A → TracialMatrixQuotient X atTop)
    (hsmul : ∀ (c : ℂ) (a : A), Φ (c • a) = c • Φ a) :
    Φ 0 = 0 := by
  have h := hsmul 0 0
  rwa [zero_smul, zero_smul] at h

/-- **Span transport.**  Representatives with convergent coordinate traces
propagate from a set to its ℂ-linear span: representatives add and scale by
hand, the coordinate traces follow by linearity of the normalized trace, and
the classes follow by additivity and homogeneity of `Φ`. -/
theorem exists_rep_tendsto_of_span
    (Φ : A → TracialMatrixQuotient X atTop)
    (hadd : ∀ a b : A, Φ (a + b) = Φ a + Φ b)
    (hsmul : ∀ (c : ℂ) (a : A), Φ (c • a) = c • Φ a)
    (τ : A →L[ℂ] ℂ) (D : Set A)
    (hbase : ∀ b ∈ D, ∃ p : ModelBoundedSequence X,
      tracialMatrixQuotientMk X atTop p = Φ b ∧
      Tendsto (fun n ↦ τ b - normTrace (X n) (p n)) atTop (nhds 0))
    {b : A} (hb : b ∈ Submodule.span ℂ D) :
    ∃ p : ModelBoundedSequence X,
      tracialMatrixQuotientMk X atTop p = Φ b ∧
      Tendsto (fun n ↦ τ b - normTrace (X n) (p n)) atTop (nhds 0) := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hbase x hx
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · rw [map_zero, phi_zero Φ hsmul]
      · refine tendsto_const_nhds.congr fun n ↦ ?_
        rw [map_zero, modelSeq_zero_apply, normTrace_zero, sub_zero]
  | add x y _ _ ihx ihy =>
      obtain ⟨p, hpk, hpt⟩ := ihx
      obtain ⟨q, hqk, hqt⟩ := ihy
      refine ⟨p + q, ?_, ?_⟩
      · rw [map_add, hpk, hqk, ← hadd]
      · have h0 : Tendsto (fun n ↦ (τ x - normTrace (X n) (p n))
            + (τ y - normTrace (X n) (q n))) atTop (nhds 0) := by
          simpa using hpt.add hqt
        refine h0.congr fun n ↦ ?_
        rw [map_add, modelSeq_add_apply, normTrace_add]
        ring
  | smul c x _ ih =>
      obtain ⟨p, hpk, hpt⟩ := ih
      refine ⟨c • p, ?_, ?_⟩
      · rw [← smul_tracialMatrixQuotientMk, hpk, ← hsmul]
      · have h0 : Tendsto (fun n ↦ c * (τ x - normTrace (X n) (p n)))
            atTop (nhds 0) := by
          simpa using hpt.const_mul c
        refine h0.congr fun n ↦ ?_
        rw [map_smul, modelSeq_smul_apply, normTrace_smul, smul_eq_mul]
        ring

/-- **The `ε/3` crossing.**  For a contractive additive homogeneous `Φ` into
the `atTop` tracial quotient and a continuous functional `τ` whose trace
clause holds on a dense-spanning set `D`, the trace clause holds for the
`qrep` model at every element of `A`.

The additive `+1` slack of `qrep_norm_lt` never appears: the comparison at
tolerance `δ` chooses a **fresh** representative of `Φ (a - b)` within `δ` of
the quotient-norm infimum, and contractivity turns that into `‖a - b‖ + δ`,
which scales. -/
theorem tendsto_norm_trace_qrep
    (Φ : A → TracialMatrixQuotient X atTop)
    (hadd : ∀ a b : A, Φ (a + b) = Φ a + Φ b)
    (hsmul : ∀ (c : ℂ) (a : A), Φ (c • a) = c • Φ a)
    (hnorm : ∀ a : A, ‖Φ a‖ ≤ ‖a‖)
    (τ : A →L[ℂ] ℂ) (D : Set A)
    (hdense : Dense (↑(Submodule.span ℂ D) : Set A))
    (hbase : ∀ b ∈ D, ∃ p : ModelBoundedSequence X,
      tracialMatrixQuotientMk X atTop p = Φ b ∧
      Tendsto (fun n ↦ τ b - normTrace (X n) (p n)) atTop (nhds 0))
    (a : A) :
    Tendsto (fun n ↦ ‖τ a - normTrace (X n) (qrep Φ a n)‖) atTop (nhds 0)
    := by
  refine tendsto_zero_of_forall_eventually_lt (fun n ↦ norm_nonneg _) ?_
  intro ε hε
  have hCpos : (0 : ℝ) < ‖τ‖ + 4 := by positivity
  set δ : ℝ := ε / (‖τ‖ + 4) with hδdef
  have hδpos : 0 < δ := div_pos hε hCpos
  obtain ⟨b, hball, hbmem⟩ :=
    (Metric.dense_iff.mp hdense a δ hδpos)
  have hbdist : ‖a - b‖ < δ := by
    rw [Metric.mem_ball] at hball
    rw [← dist_eq_norm, dist_comm]
    exact hball
  obtain ⟨p, hpk, hpt⟩ :=
    exists_rep_tendsto_of_span Φ hadd hsmul τ D hbase hbmem
  obtain ⟨r, hrk, hrn⟩ := exists_rep_norm_lt (Φ (a - b)) hδpos
  have hrbound : ‖r‖ < 2 * δ := by
    have h1 : ‖Φ (a - b)‖ ≤ ‖a - b‖ := hnorm _
    have h2 : ‖r‖ < ‖Φ (a - b)‖ + δ := hrn
    linarith
  have hnull : IsHilbertSchmidtNull X atTop (qrep Φ a - p - r) := by
    refine (tracialMatrixQuotientMk_eq_zero_iff X atTop _).mp ?_
    rw [map_sub, map_sub, qrep_mk, hpk, hrk, phi_sub Φ hadd hsmul a b]
    abel
  have hev1 := eventually_lt_of_tendsto_zero hnull hδpos
  have hptnorm : Tendsto (fun n ↦ ‖τ b - normTrace (X n) (p n)‖) atTop
      (nhds 0) := by
    refine tendsto_zero_of_forall_eventually_lt (fun n ↦ norm_nonneg _) ?_
    intro ε' hε'
    filter_upwards [Metric.tendsto_nhds.mp hpt ε' hε'] with n hn
    rwa [dist_zero_right] at hn
  have hev2 := eventually_lt_of_tendsto_zero hptnorm hδpos
  filter_upwards [hev1, hev2] with n h1 h2
  have hsplitτ : τ a - normTrace (X n) (qrep Φ a n)
      = τ (a - b) + (τ b - normTrace (X n) (p n))
        - (normTrace (X n) (qrep Φ a n) - normTrace (X n) (p n)) := by
    rw [map_sub]
    ring
  have hsplittr : normTrace (X n) (qrep Φ a n) - normTrace (X n) (p n)
      = normTrace (X n) ((qrep Φ a - p - r) n) + normTrace (X n) (r n) := by
    have e1 : normTrace (X n) ((qrep Φ a - p - r) n)
        = normTrace (X n) (qrep Φ a n) - normTrace (X n) (p n)
          - normTrace (X n) (r n) := by
      rw [modelSeq_sub_apply, modelSeq_sub_apply, normTrace_sub, normTrace_sub]
    rw [e1]
    ring
  have hb1 : ‖normTrace (X n) ((qrep Φ a - p - r) n)‖
      ≤ hsNorm (X n) ((qrep Φ a - p - r) n) :=
    norm_normTrace_le_hsNorm (X n) _
  have hb2 : ‖normTrace (X n) (r n)‖ ≤ ‖r n‖ :=
    PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm (X n) (r n)
  have hb2' : ‖r n‖ ≤ ‖r‖ :=
    boundedMatrixSequence_coord_norm_le (fun n ↦ X n) r n
  have hτab : ‖τ (a - b)‖ ≤ ‖τ‖ * ‖a - b‖ := τ.le_opNorm _
  have hτab' : ‖τ (a - b)‖ ≤ ‖τ‖ * δ := by
    refine hτab.trans ?_
    exact mul_le_mul_of_nonneg_left hbdist.le (norm_nonneg τ)
  have htr : ‖normTrace (X n) (qrep Φ a n) - normTrace (X n) (p n)‖
      < 3 * δ := by
    rw [hsplittr]
    calc ‖normTrace (X n) ((qrep Φ a - p - r) n) + normTrace (X n) (r n)‖
        ≤ ‖normTrace (X n) ((qrep Φ a - p - r) n)‖
          + ‖normTrace (X n) (r n)‖ := norm_add_le _ _
      _ < δ + 2 * δ := by
          have hx : ‖normTrace (X n) ((qrep Φ a - p - r) n)‖ < δ :=
            lt_of_le_of_lt hb1 h1
          have hy : ‖normTrace (X n) (r n)‖ < 2 * δ :=
            lt_of_le_of_lt (hb2.trans hb2') hrbound
          linarith
      _ = 3 * δ := by ring
  have hfinal : ‖τ a - normTrace (X n) (qrep Φ a n)‖
      < ‖τ‖ * δ + δ + 3 * δ := by
    rw [hsplitτ]
    calc ‖τ (a - b) + (τ b - normTrace (X n) (p n))
          - (normTrace (X n) (qrep Φ a n) - normTrace (X n) (p n))‖
        ≤ ‖τ (a - b) + (τ b - normTrace (X n) (p n))‖
          + ‖normTrace (X n) (qrep Φ a n) - normTrace (X n) (p n)‖ :=
          norm_sub_le _ _
      _ ≤ ‖τ (a - b)‖ + ‖τ b - normTrace (X n) (p n)‖
          + ‖normTrace (X n) (qrep Φ a n) - normTrace (X n) (p n)‖ := by
          have := norm_add_le (τ (a - b)) (τ b - normTrace (X n) (p n))
          linarith
      _ < ‖τ‖ * δ + δ + 3 * δ := by
          linarith [hτab', h2, htr]
  have hεeq : ‖τ‖ * δ + δ + 3 * δ ≤ ε := by
    have hmul : (‖τ‖ + 4) * δ = ε := by
      rw [hδdef]
      field_simp
    linarith [hmul]
  exact lt_of_lt_of_le hfinal hεeq

end Crossing

/-! ## C. The assembly: any contractive lift makes the canonical trace
hyperlinear -/

section Assembly

variable {G : Type} [Group G]

/-- **Everything the sofic hyperlinear-trace bridge needs, except the
C-star instance.**  Given any map `Φ` out of `C*(G)` that is additive,
homogeneous, multiplicative, `⋆`-compatible and contractive into the `atTop`
tracial quotient, and whose generator trace clauses hold, the canonical trace
of `C*(G)` is hyperlinear in Shulman's sequential sense.

The universal property of `C*(G)` produces such a `Φ` from
`soficUnitaryHom` the moment the quotient carries its `CStarAlgebra`
instance; contractivity is then automatic for a ⋆-homomorphism between
C-star algebras.  Neither fact is assumed here. -/
theorem isHyperlinearTrace_canonicalMaximalTrace_of_lift
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (Φ : MaximalGroupCStar G → TracialMatrixQuotient X atTop)
    (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b)
    (hsmul : ∀ (c : ℂ) a, Φ (c • a) = c • Φ a)
    (hmul : ∀ a b, Φ (a * b) = Φ a * Φ b)
    (hstar : ∀ a, Φ (star a) = star (Φ a))
    (hnorm : ∀ a, ‖Φ a‖ ≤ ‖a‖)
    (hgen : ∀ g : G, ∃ p : ModelBoundedSequence X,
      tracialMatrixQuotientMk X atTop p = Φ (maximalGroupCStarGenerator G g) ∧
      Tendsto (fun n ↦ canonicalMaximalTrace G (maximalGroupCStarGenerator G g)
        - normTrace (X n) (p n)) atTop (nhds 0)) :
    IsHyperlinearTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) := by
  refine isHyperlinearTrace_of_representation Φ hadd hsmul hmul hstar ?_
  intro a
  refine tendsto_norm_trace_qrep Φ hadd hsmul hnorm (canonicalMaximalTrace G)
    (Set.range (maximalGroupCStarGenerator G))
    (maximalGroupCStar_dense_span_generator G) ?_ a
  rintro _ ⟨g, rfl⟩
  exact hgen g

/-- **The sofic hypotheses of the bridge, discharged.**  Any ⋆-homomorphism
`π` out of `C*(G)` that restricts to the sofic unitary classes on the
generators and is contractive makes the canonical trace hyperlinear: the
generator trace clauses are the fixed-point computations of
`Sofic/SoficPermutationTrace.lean`.

The two hypotheses are exactly what `maximalGroupCStar_existsUnique_lift`
applied to `soficUnitaryHom` and ⋆-homomorphism contractivity will produce
once the `atTop` tracial quotient has its `CStarAlgebra` instance.  This
theorem is the entire remaining content of the bridge; the eventual pinned
`canonicalMaximalTrace_isHyperlinearTrace_of_isSofic` is its instantiation. -/
theorem isHyperlinearTrace_canonicalMaximalTrace_of_soficRepresentation
    (S : SoficApproximation G) [∀ n, Nonempty (S.model n)]
    (hpos : ∀ n, 0 < Fintype.card (S.model n))
    (π : MaximalGroupCStar G →⋆ₐ[ℂ]
      TracialMatrixQuotient (fun n ↦ S.model n) atTop)
    (hπgen : ∀ g : G, π (maximalGroupCStarGenerator G g)
      = tracialMatrixQuotientMk (fun n ↦ S.model n) atTop (soficUnitarySeq S g))
    (hπnorm : ∀ a, ‖π a‖ ≤ ‖a‖) :
    IsHyperlinearTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) := by
  refine isHyperlinearTrace_canonicalMaximalTrace_of_lift (fun a ↦ π a)
    (fun a b ↦ map_add π a b) (fun c a ↦ map_smul π c a)
    (fun a b ↦ map_mul π a b) (fun a ↦ map_star π a) hπnorm ?_
  intro g
  refine ⟨soficUnitarySeq S g, (hπgen g).symm, ?_⟩
  by_cases hg : g = 1
  · subst hg
    rw [canonicalMaximalTrace_generator_one]
    have h1 : Tendsto (fun n ↦ (1 : ℂ)
        - normTrace (S.model n) (modelUnitary S n 1)) atTop (nhds 0) := by
      have hc : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds (1 : ℂ)) :=
        tendsto_const_nhds
      have := hc.sub (tendsto_normTrace_modelUnitary_one S hpos)
      simpa using this
    refine h1.congr fun n ↦ ?_
    rw [soficUnitarySeq_apply]
  · rw [canonicalMaximalTrace_generator_of_ne_one G hg]
    have h0 : Tendsto (fun n ↦ (0 : ℂ)
        - normTrace (S.model n) (modelUnitary S n g)) atTop (nhds 0) := by
      have hc : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (nhds (0 : ℂ)) :=
        tendsto_const_nhds
      have := hc.sub
        (tendsto_normTrace_modelUnitary_of_ne_one S hpos hg)
      simpa using this
    refine h0.congr fun n ↦ ?_
    rw [soficUnitarySeq_apply]

end Assembly

end

end ShulmanTrace
end GroupApproximation
