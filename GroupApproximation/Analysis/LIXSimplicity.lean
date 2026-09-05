import GroupApproximation.Analysis.CStarSimple
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Simplicity of a unital increasing union whose stages become full

Let `B` be a unital C⋆-algebra which is the closure of an increasing union of closed
⋆-subalgebras `S i`.  This module proves that `B` is simple — `IsSimpleCStar B`, every nonzero
closed two-sided ideal is all of `B` — as soon as every nonzero positive element of every stage
is *full*.

That is the structural half of the argument for STW Problem LIX.  The twisted AH tower there is
built so that a point-evaluation summand at a later stage makes every nonzero positive element of
an earlier stage full, and simplicity of the limit is what turns a finite-stage
non-null-homotopic unitary into a statement about *simple* C⋆-algebras.  Nothing below mentions
that tower: the theorem is unconditional and about an arbitrary increasing union.

## The route, and why it is not the manuscript's

The manuscript argues through the quotient `A / J`: the approximant `a ∈ A_k` of a positive
`b ∈ J` need not lie in `J`, and what repairs that is the cut `c = (a - ε)₊`, which the quotient
map kills because `‖q a‖ = ‖q (a - b)‖ < ε`.

**That route is not available here.**  The repository's `Analysis/CStarIdealQuotient` gives
`B ⧸ I` a complete normed ⋆-algebra structure and says explicitly that the C⋆-identity for the
quotient norm is *not* proved — its proof runs through an approximate unit of the ideal.  Without
it there is no continuous functional calculus on `B ⧸ I`, so `q ((a - ε)₊) = (q a - ε)₊` is not a
statement one can make, let alone use.

The replacement stays inside `B` and is, if anything, shorter.  Write `p = (· - ε)₊` and
`d = cfc (√ ∘ p) a`.  Then, purely by the functional calculus of the single element `a`,

    d * (a - ε) * d = c * c,        c = cfc p a,

because `√(p t) · (t - ε) · √(p t) = p t · p t` pointwise.  From `‖a - b‖ ≤ ε` one gets
`a - ε ≤ b`, and conjugating by the positive `d` gives

    c * c ≤ d * b * d ∈ I.

So the whole argument reduces to one lemma: a closed two-sided ideal is **hereditary** in the
form `0 ≤ s`, `s * s ≤ v ∈ I ⟹ s ∈ I`.  That lemma is proved here (`mem_of_mul_self_le`) by the
resolvent approximate unit `r_δ = δ (v + δ)⁻¹` of the ideal element `v`, realized through the
functional calculus of `v` so that no inverse has to be produced by hand:

* `1 - r_δ = v · (v + δ)⁻¹` lies in `I` because `I` is a left ideal;
* `‖s r_δ‖² = ‖r_δ (s s) r_δ‖ ≤ ‖r_δ v r_δ‖ ≤ δ`, the last step being the elementary scalar
  bound `δ² t / (t + δ)² ≤ δ` on `[0, ∞)`;
* so `s` is a norm limit of `s (1 - r_δ) ∈ I`, and `I` is closed.

Star-stability of the ideal is **not** assumed anywhere — which matters, because
`IsSimpleCStar` of `Analysis/CStarSimple` quantifies over closed two-sided ideals with no
⋆-hypothesis, and a theorem that produced only ⋆-stable-ideal simplicity would not instantiate
it.

## What is proved

* `cfc_mem_of_isClosed` — a closed ⋆-subalgebra absorbs the continuous functional calculus of its
  selfadjoint elements.
* `IsFull`, `IsFullIn` — fullness in `B` and fullness inside a stage, both as concrete finite
  sums `∑ xᵢ a yᵢ` so that no ideal-generation API is involved; `one_mem_of_isFull`.
* `mem_of_mul_self_le` — closed two-sided ideals are hereditary, in the form used.
* `exists_ge_nonneg_mem_approx` — a positive element of `B` is approximated by a positive element
  of an arbitrarily late stage.
* `exists_ge_mem_ideal_of_nonneg` — a nonzero closed two-sided ideal meets some stage in a
  nonzero positive element.
* `eq_top_of_stagewise_full`, `isSimpleCStar_of_stagewise_full` — the simplicity theorem.

## Manuscript status

Lemma 5 of `research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`, the
simplicity half, less the input "every nonzero positive element of a stage becomes full", which
is the tower-specific hypothesis and belongs to the stage lane.
-/

namespace GroupApproximation

namespace LIX

noncomputable section

/-! ### The two scalar functions -/

/-- The cut `t ↦ (t - r)₊`.  Applied through the functional calculus to a positive `a`, it kills
the part of the spectrum below `r` and leaves the rest strictly positive. -/
def posCut (r : ℝ) : ℝ → ℝ := fun t => max (t - r) 0

theorem continuous_posCut (r : ℝ) : Continuous (posCut r) :=
  (continuous_id.sub continuous_const).max continuous_const

theorem posCut_nonneg (r t : ℝ) : 0 ≤ posCut r t := le_max_right _ _

theorem posCut_eq_zero {r t : ℝ} (h : t ≤ r) : posCut r t = 0 := max_eq_right (sub_nonpos.mpr h)

theorem posCut_eq_sub {r t : ℝ} (h : r ≤ t) : posCut r t = t - r :=
  max_eq_left (sub_nonneg.mpr h)

theorem posCut_pos {r t : ℝ} (h : r < t) : 0 < posCut r t :=
  lt_max_iff.mpr (Or.inl (by linarith))

/-- The square root of the cut.  Naming it keeps it a head symbol, which the rewriting inside
`exists_ge_mem_ideal_of_nonneg` needs. -/
def sqrtPosCut (r : ℝ) : ℝ → ℝ := fun t => Real.sqrt (posCut r t)

theorem continuous_sqrtPosCut (r : ℝ) : Continuous (sqrtPosCut r) :=
  (continuous_posCut r).sqrt

theorem sqrtPosCut_nonneg (r t : ℝ) : 0 ≤ sqrtPosCut r t := Real.sqrt_nonneg _

/-- The pointwise identity behind `d * (a - ε) * d = c * c`. -/
theorem sqrtPosCut_mul_sub_mul (r t : ℝ) :
    sqrtPosCut r t * (t - r) * sqrtPosCut r t = posCut r t * posCut r t := by
  have hsq : sqrtPosCut r t * sqrtPosCut r t = posCut r t :=
    Real.mul_self_sqrt (posCut_nonneg r t)
  have step : sqrtPosCut r t * (t - r) * sqrtPosCut r t = posCut r t * (t - r) := by
    calc sqrtPosCut r t * (t - r) * sqrtPosCut r t
        = sqrtPosCut r t * sqrtPosCut r t * (t - r) := by ring
      _ = posCut r t * (t - r) := by rw [hsq]
  rw [step]
  rcases le_or_lt t r with h | h
  · rw [posCut_eq_zero h]; ring
  · rw [posCut_eq_sub h.le]

/-- The resolvent cut-off `t ↦ δ / (max t 0 + δ)`.  The `max t 0` makes it continuous on all of
`ℝ`, so the functional calculus needs no side condition; on the spectrum of a positive element it
is `t ↦ δ / (t + δ)`, i.e. `r_δ = δ (v + δ)⁻¹`. -/
def resCut (δ : ℝ) : ℝ → ℝ := fun t => δ / (max t 0 + δ)

theorem denom_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < max t 0 + δ := by
  have : (0 : ℝ) ≤ max t 0 := le_max_right _ _
  linarith

theorem continuous_resCut {δ : ℝ} (hδ : 0 < δ) : Continuous (resCut δ) :=
  continuous_const.div ((continuous_id.max continuous_const).add continuous_const)
    fun t => (denom_pos hδ t).ne'

theorem resCut_nonneg' {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ resCut δ t :=
  div_nonneg hδ.le (denom_pos hδ t).le

/-- The cofactor of the resolvent cut: `1 - resCut δ t = t * invCut δ t` on `[0, ∞)`.  Written
with a division rather than an inverse so that its continuity is the same one-liner. -/
def invCut (δ : ℝ) : ℝ → ℝ := fun t => 1 / (max t 0 + δ)

theorem continuous_invCut {δ : ℝ} (hδ : 0 < δ) : Continuous (invCut δ) :=
  continuous_const.div ((continuous_id.max continuous_const).add continuous_const)
    fun t => (denom_pos hδ t).ne'

/-! ### A closed ⋆-subalgebra absorbs the continuous functional calculus -/

section Subalgebra

variable {B : Type*} [CStarAlgebra B]

/-- A closed ⋆-subalgebra of a C⋆-algebra contains `cfc f a` whenever it contains the selfadjoint
element `a` and `f` is continuous.  Spectral permanence is not needed: the function is asked to
be continuous everywhere, so the calculus computed inside the subalgebra — itself a C⋆-algebra —
transports along the inclusion by `StarAlgHomClass.map_cfc`. -/
theorem cfc_mem_of_isClosed {T : StarSubalgebra ℂ B} (hT : IsClosed (T : Set B))
    {f : ℝ → ℝ} (hf : Continuous f) {a : B} (ha : a ∈ T) (ha' : IsSelfAdjoint a) :
    cfc f a ∈ T := by
  haveI : IsClosed (T : Set B) := hT
  have hsa : IsSelfAdjoint (⟨a, ha⟩ : T) := Subtype.ext ha'
  have hcont : Continuous (T.subtype : T → B) := by
    rw [StarSubalgebra.coe_subtype]
    exact continuous_subtype_val
  have hmap : (T.subtype (cfc f (⟨a, ha⟩ : T)) : B) = cfc f a :=
    StarAlgHomClass.map_cfc (S := ℂ) T.subtype f (⟨a, ha⟩ : T) hf.continuousOn hcont hsa ha'
  rw [← hmap]
  exact (cfc f (⟨a, ha⟩ : T)).2

end Subalgebra

/-! ### Fullness -/

section Full

variable {B : Type*} [CStarAlgebra B]

/-- `a` is **full** in `B`: the closed two-sided ideal it generates is all of `B`.  Stated
concretely, so that no ideal-generation API is involved — `1` is a limit of finite sums
`∑ xᵢ a yᵢ`. -/
def IsFull (a : B) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (x y : Fin n → B), ‖1 - ∑ i, x i * a * y i‖ < ε

/-- `a` is **full in the subalgebra `T`**: the same finite sums, with every coefficient taken
from `T`.  This is the form a stage of an inductive system supplies, and
`IsFullIn.isFull` forgets the memberships. -/
def IsFullIn (T : StarSubalgebra ℂ B) (a : B) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (x y : Fin n → B),
    (∀ i, x i ∈ T) ∧ (∀ i, y i ∈ T) ∧ ‖1 - ∑ i, x i * a * y i‖ < ε

/-- Fullness inside a subalgebra is fullness: the witnessing sums are the same, and the unit of a
`StarSubalgebra` is the unit of the ambient algebra. -/
theorem IsFullIn.isFull {T : StarSubalgebra ℂ B} {a : B} (h : IsFullIn T a) : IsFull a := by
  intro ε hε
  obtain ⟨n, x, y, -, -, hxy⟩ := h ε hε
  exact ⟨n, x, y, hxy⟩

/-- The cheapest way to produce fullness in a stage: an exact finite expression of the unit. -/
theorem isFullIn_of_sum_eq_one {T : StarSubalgebra ℂ B} {a : B} {n : ℕ} {x y : Fin n → B}
    (hx : ∀ i, x i ∈ T) (hy : ∀ i, y i ∈ T) (h : ∑ i, x i * a * y i = 1) : IsFullIn T a :=
  fun ε hε => ⟨n, x, y, hx, hy, by simpa [h] using hε⟩

/-- The same for fullness in the ambient algebra. -/
theorem isFull_of_sum_eq_one {a : B} {n : ℕ} {x y : Fin n → B}
    (h : ∑ i, x i * a * y i = 1) : IsFull a :=
  fun ε hε => ⟨n, x, y, by simpa [h] using hε⟩

/-- A full element of a closed two-sided ideal forces the ideal to contain the unit. -/
theorem one_mem_of_isFull {I : Ideal B} [I.IsTwoSided] (hI : IsClosed (I : Set B))
    {a : B} (ha : a ∈ I) (hfull : IsFull a) : (1 : B) ∈ I := by
  have h1 : (1 : B) ∈ closure (I : Set B) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, x, y, hxy⟩ := hfull ε hε
    refine ⟨∑ i, x i * a * y i, ?_, ?_⟩
    · exact SetLike.mem_coe.mpr
        (sum_mem fun i _ => Ideal.mul_mem_right _ I (Ideal.mul_mem_left I _ ha))
    · rwa [dist_eq_norm]
  rwa [hI.closure_eq] at h1

end Full

/-! ### Closed two-sided ideals are hereditary -/

section Hereditary

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- `r_δ = δ (v + δ)⁻¹` is positive. -/
theorem resCut_nonneg (v : B) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ cfc (resCut δ) v :=
  cfc_nonneg fun t _ => resCut_nonneg' hδ t

/-- `1 - r_δ = v (v + δ)⁻¹` lies in any left ideal containing `v`.  Both sides are computed in
the functional calculus of `v`, so no inverse is produced by hand. -/
theorem one_sub_resCut_eq {v : B} (hv : 0 ≤ v) {δ : ℝ} (hδ : 0 < δ) :
    (1 : B) - cfc (resCut δ) v = v * cfc (invCut δ) v := by
  have hrcont : Continuous (resCut δ) := continuous_resCut hδ
  have hicont : Continuous (invCut δ) := continuous_invCut hδ
  have hL : (1 : B) - cfc (resCut δ) v = cfc (fun t : ℝ => 1 - resCut δ t) v := by
    rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (resCut δ) v (by fun_prop) hrcont.continuousOn,
      cfc_const (1 : ℝ) v, map_one]
  have hR : v * cfc (invCut δ) v = cfc (fun t : ℝ => t * invCut δ t) v := by
    rw [cfc_mul (fun t : ℝ => t) (invCut δ) v (by fun_prop) hicont.continuousOn, cfc_id' ℝ v]
  rw [hL, hR]
  refine cfc_congr fun t ht => ?_
  have h0 : (0 : ℝ) ≤ t := spectrum_nonneg_of_nonneg hv ht
  have hmax : max t 0 = t := max_eq_left h0
  have hne : t + δ ≠ 0 := ne_of_gt (by linarith)
  have hcancel : (t + δ) * (t + δ)⁻¹ = 1 := mul_inv_cancel₀ hne
  simp only [resCut, invCut, hmax, div_eq_mul_inv, one_mul]
  calc (1 : ℝ) - δ * (t + δ)⁻¹
      = (t + δ) * (t + δ)⁻¹ - δ * (t + δ)⁻¹ := by rw [hcancel]
    _ = t * (t + δ)⁻¹ := by ring

/-- The scalar bound `δ² t / (t + δ)² ≤ δ` on `[0, ∞)`, transported by the functional calculus:
`‖r_δ v r_δ‖ ≤ δ`. -/
theorem norm_resCut_conj_le {v : B} (hv : 0 ≤ v) {δ : ℝ} (hδ : 0 < δ) :
    ‖cfc (resCut δ) v * v * cfc (resCut δ) v‖ ≤ δ := by
  have hrcont : Continuous (resCut δ) := continuous_resCut hδ
  have heq : cfc (resCut δ) v * v * cfc (resCut δ) v
      = cfc (fun t : ℝ => resCut δ t * t * resCut δ t) v := by
    rw [cfc_mul (fun t : ℝ => resCut δ t * t) (resCut δ) v
        ((hrcont.mul continuous_id).continuousOn) hrcont.continuousOn,
      cfc_mul (resCut δ) (fun t : ℝ => t) v hrcont.continuousOn (by fun_prop), cfc_id' ℝ v]
  rw [heq]
  refine norm_cfc_le hδ.le fun t ht => ?_
  have h0 : (0 : ℝ) ≤ t := spectrum_nonneg_of_nonneg hv ht
  have hmax : max t 0 = t := max_eq_left h0
  have hpos : (0 : ℝ) < t + δ := by linarith
  have hnn : 0 ≤ δ / (t + δ) * t * (δ / (t + δ)) :=
    mul_nonneg (mul_nonneg (div_nonneg hδ.le hpos.le) h0) (div_nonneg hδ.le hpos.le)
  have hb : δ * t ≤ (t + δ) * (t + δ) := by
    nlinarith [sq_nonneg t, sq_nonneg δ, mul_nonneg h0 hδ.le]
  simp only [resCut, hmax, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [div_mul_eq_mul_div, div_mul_div_comm, div_le_iff₀ (mul_pos hpos hpos)]
  calc δ * t * δ = δ * (δ * t) := by ring
    _ ≤ δ * ((t + δ) * (t + δ)) := mul_le_mul_of_nonneg_left hb hδ.le

/-- **Closed two-sided ideals are hereditary**, in the form the cut-down argument needs: if
`0 ≤ s` and `s * s ≤ v` with `v` in the ideal, then `s` is in the ideal.

`s` is a norm limit of `s (1 - r_δ)`, which lies in the ideal because `1 - r_δ` does; the error
`‖s r_δ‖` is controlled by the C⋆-identity, `‖s r_δ‖² = ‖r_δ (s s) r_δ‖ ≤ ‖r_δ v r_δ‖ ≤ δ`. -/
theorem mem_of_mul_self_le {I : Ideal B} [I.IsTwoSided] (hI : IsClosed (I : Set B))
    {s v : B} (hs : 0 ≤ s) (hsv : s * s ≤ v) (hv : v ∈ I) : s ∈ I := by
  have hssa : star s = s := (IsSelfAdjoint.of_nonneg hs).star_eq
  have hssnn : (0 : B) ≤ s * s := by
    have h := star_mul_self_nonneg s
    rwa [hssa] at h
  have hv0 : (0 : B) ≤ v := hssnn.trans hsv
  rw [← hI.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ε ^ 2 :=
    ⟨ε ^ 2 / 2, div_pos (pow_pos hε 2) (by norm_num), by linarith [pow_pos hε 2]⟩
  refine ⟨s * (1 - cfc (resCut δ) v), ?_, ?_⟩
  · rw [one_sub_resCut_eq hv0 hδ, ← mul_assoc]
    exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ I (Ideal.mul_mem_left I s hv))
  · have hr0 : (0 : B) ≤ cfc (resCut δ) v := resCut_nonneg v hδ
    have hrsa : IsSelfAdjoint (cfc (resCut δ) v) := cfc_predicate _ _
    have hdiff : s - s * (1 - cfc (resCut δ) v) = s * cfc (resCut δ) v := by
      rw [mul_sub, mul_one]
      abel
    have hstar : star (s * cfc (resCut δ) v) * (s * cfc (resCut δ) v)
        = cfc (resCut δ) v * (s * s) * cfc (resCut δ) v := by
      rw [star_mul, hssa, hrsa.star_eq]
      simp only [mul_assoc]
    have hsq : ‖s * cfc (resCut δ) v‖ * ‖s * cfc (resCut δ) v‖ ≤ δ := by
      calc ‖s * cfc (resCut δ) v‖ * ‖s * cfc (resCut δ) v‖
          = ‖star (s * cfc (resCut δ) v) * (s * cfc (resCut δ) v)‖ :=
            CStarRing.norm_star_mul_self.symm
        _ = ‖cfc (resCut δ) v * (s * s) * cfc (resCut δ) v‖ := by rw [hstar]
        _ ≤ ‖cfc (resCut δ) v * v * cfc (resCut δ) v‖ :=
            CStarAlgebra.norm_le_norm_of_nonneg_of_le (conjugate_nonneg_of_nonneg hssnn hr0)
              (conjugate_le_conjugate_of_nonneg hsv hr0)
        _ ≤ δ := norm_resCut_conj_le hv0 hδ
    have hxnn : (0 : ℝ) ≤ ‖s * cfc (resCut δ) v‖ := norm_nonneg _
    rw [dist_eq_norm, hdiff]
    nlinarith [hsq, hδε, hxnn, hε]

end Hereditary

/-! ### Positive approximation inside a stage -/

section Approx

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {ι : Type*} [SemilatticeSup ι] {S : ι → StarSubalgebra ℂ B}

/-- A positive element of `B` is approximated, to any accuracy, by a positive element of an
arbitrarily late stage: approximate its square root by an element `z` of the dense union and take
`z⋆ z`, positive by construction and close to `(√b)⋆ √b = b`. -/
theorem exists_ge_nonneg_mem_approx (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    (k : ι) {b : B} (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, k ≤ j ∧ ∃ a : B, a ∈ S j ∧ 0 ≤ a ∧ ‖a - b‖ < ε := by
  obtain ⟨s, hs0, hss⟩ : ∃ s : B, 0 ≤ s ∧ s * s = b := by
    refine ⟨cfc Real.sqrt b, cfc_nonneg fun t _ => Real.sqrt_nonneg t, ?_⟩
    calc cfc Real.sqrt b * cfc Real.sqrt b
        = cfc (fun t : ℝ => Real.sqrt t * Real.sqrt t) b :=
          (cfc_mul Real.sqrt Real.sqrt b Real.continuous_sqrt.continuousOn
            Real.continuous_sqrt.continuousOn).symm
      _ = cfc (id : ℝ → ℝ) b :=
          cfc_congr fun t ht => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hb ht)
      _ = b := cfc_id ℝ b
  have hsa : star s = s := (IsSelfAdjoint.of_nonneg hs0).star_eq
  have hCpos : (0 : ℝ) < 2 * (‖s‖ + 1) := by positivity
  obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 2 * (‖s‖ + 1) * δ ≤ ε := by
    refine ⟨min 1 (ε / (2 * (‖s‖ + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have hle : min 1 (ε / (2 * (‖s‖ + 1))) ≤ ε / (2 * (‖s‖ + 1)) := min_le_right _ _
    have hEq : 2 * (‖s‖ + 1) * (ε / (2 * (‖s‖ + 1))) = ε := by field_simp
    calc 2 * (‖s‖ + 1) * min 1 (ε / (2 * (‖s‖ + 1)))
        ≤ 2 * (‖s‖ + 1) * (ε / (2 * (‖s‖ + 1))) := mul_le_mul_of_nonneg_left hle hCpos.le
      _ = ε := hEq
  obtain ⟨z, hz₁, hz₂⟩ := Metric.dense_iff.mp hdense s δ hδ0
  obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz₂
  have hzS : z ∈ S (k ⊔ i) := hmono le_sup_right hzi
  have hzd : ‖z - s‖ < δ := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hz₁
  have hzn : ‖z‖ ≤ ‖s‖ + δ := by
    have h : ‖z‖ ≤ ‖s‖ + ‖z - s‖ := by simpa using norm_add_le s (z - s)
    linarith
  refine ⟨k ⊔ i, le_sup_left, star z * z, mul_mem (star_mem hzS) hzS,
    star_mul_self_nonneg z, ?_⟩
  have key : star z * z - b = star z * (z - s) + star (z - s) * s := by
    rw [← hss, star_sub, hsa]
    ring
  have hnn : (0 : ℝ) ≤ ‖z - s‖ := norm_nonneg _
  have hsn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg _
  calc ‖star z * z - b‖
      ≤ ‖star z * (z - s)‖ + ‖star (z - s) * s‖ := by
        rw [key]; exact norm_add_le _ _
    _ ≤ ‖star z‖ * ‖z - s‖ + ‖star (z - s)‖ * ‖s‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = (‖z‖ + ‖s‖) * ‖z - s‖ := by rw [norm_star, norm_star]; ring
    _ ≤ 2 * (‖s‖ + 1) * ‖z - s‖ :=
        mul_le_mul_of_nonneg_right (by linarith) hnn
    _ < 2 * (‖s‖ + 1) * δ := mul_lt_mul_of_pos_left hzd hCpos
    _ ≤ ε := hδε

end Approx

/-! ### A nonzero ideal meets a stage -/

section Ideal

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial B]
variable {ι : Type*} [SemilatticeSup ι] {S : ι → StarSubalgebra ℂ B}

/-- **A nonzero closed two-sided ideal meets some stage in a nonzero positive element.**

The approximant `a ∈ S j` of a positive `b ∈ I` need not itself lie in `I`; the cut
`c = (a - ε)₊` with `ε = ‖b‖/4` repairs that.  With `d = cfc (√ ∘ (· - ε)₊) a`, the functional
calculus of the single element `a` gives `d (a - ε) d = c c` exactly, while `‖a - b‖ < ε` gives
`a - ε ≤ b`; conjugating by the positive `d` puts `c c` below `d b d ∈ I`, and closed two-sided
ideals are hereditary.  On the other side `‖a‖ > 3‖b‖/4 > ε` lies in the spectrum of `a`, so the
spectrum of `c` contains a strictly positive point and `c ≠ 0`. -/
theorem exists_ge_mem_ideal_of_nonneg (hclosed : ∀ i, IsClosed (S i : Set B))
    (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    {I : Ideal B} [I.IsTwoSided] (hIclosed : IsClosed (I : Set B))
    {b : B} (hbI : b ∈ I) (hb0 : 0 ≤ b) (hbne : b ≠ 0) (k : ι) :
    ∃ j, k ≤ j ∧ ∃ c : B, c ∈ S j ∧ c ∈ I ∧ 0 ≤ c ∧ c ≠ 0 := by
  have hM : 0 < ‖b‖ := norm_pos_iff.mpr hbne
  obtain ⟨j, hkj, a, haS, ha0, haε⟩ :=
    exists_ge_nonneg_mem_approx hmono hdense k hb0 (by linarith : (0 : ℝ) < ‖b‖ / 4)
  set ε : ℝ := ‖b‖ / 4 with hεdef
  have hasa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  have hbsa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg hb0
  have hpc : Continuous (posCut ε) := continuous_posCut ε
  have hsc : Continuous (sqrtPosCut ε) := continuous_sqrtPosCut ε
  -- the two functional-calculus elements, both in the stage
  have hcS : cfc (posCut ε) a ∈ S j := cfc_mem_of_isClosed (hclosed j) hpc haS hasa
  have hc0 : (0 : B) ≤ cfc (posCut ε) a := cfc_nonneg fun t _ => posCut_nonneg ε t
  have hd0 : (0 : B) ≤ cfc (sqrtPosCut ε) a := cfc_nonneg fun t _ => sqrtPosCut_nonneg ε t
  -- `d (a - ε) d = c c`, purely inside the functional calculus of `a`
  have hsub : a - algebraMap ℝ B ε = cfc (fun t : ℝ => t - ε) a := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ : ℝ => ε) a (by fun_prop) (by fun_prop), cfc_id' ℝ a,
      cfc_const ε a]
  have hL : cfc (sqrtPosCut ε) a * cfc (fun t : ℝ => t - ε) a * cfc (sqrtPosCut ε) a
      = cfc (fun t : ℝ => sqrtPosCut ε t * (t - ε) * sqrtPosCut ε t) a := by
    rw [cfc_mul (fun t : ℝ => sqrtPosCut ε t * (t - ε)) (sqrtPosCut ε) a
        ((hsc.mul (continuous_id.sub continuous_const)).continuousOn) hsc.continuousOn,
      cfc_mul (sqrtPosCut ε) (fun t : ℝ => t - ε) a hsc.continuousOn (by fun_prop)]
  have hR : cfc (posCut ε) a * cfc (posCut ε) a
      = cfc (fun t : ℝ => posCut ε t * posCut ε t) a :=
    (cfc_mul (posCut ε) (posCut ε) a hpc.continuousOn hpc.continuousOn).symm
  have hprod : cfc (sqrtPosCut ε) a * (a - algebraMap ℝ B ε) * cfc (sqrtPosCut ε) a
      = cfc (posCut ε) a * cfc (posCut ε) a := by
    rw [hsub, hL, hR]
    exact cfc_congr fun t _ => sqrtPosCut_mul_sub_mul ε t
  -- `a - ε ≤ b`
  have h1 : a - b ≤ algebraMap ℝ B ‖a - b‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (hasa.sub hbsa)
  have h2 : algebraMap ℝ B ‖a - b‖ ≤ algebraMap ℝ B ε := by
    rw [← sub_nonneg, ← map_sub, ← cfc_const (ε - ‖a - b‖) (1 : B)]
    exact cfc_nonneg fun t _ => by linarith
  have hle : a - algebraMap ℝ B ε ≤ b :=
    sub_le_iff_le_add'.mpr (sub_le_iff_le_add.mp (h1.trans h2))
  -- the cut is in the ideal
  have hconj : cfc (posCut ε) a * cfc (posCut ε) a
      ≤ cfc (sqrtPosCut ε) a * b * cfc (sqrtPosCut ε) a := by
    rw [← hprod]
    exact conjugate_le_conjugate_of_nonneg hle hd0
  have hmemI : cfc (sqrtPosCut ε) a * b * cfc (sqrtPosCut ε) a ∈ I :=
    Ideal.mul_mem_right _ I (Ideal.mul_mem_left I _ hbI)
  have hcI : cfc (posCut ε) a ∈ I := mem_of_mul_self_le hIclosed hc0 hconj hmemI
  -- the cut is nonzero
  refine ⟨j, hkj, cfc (posCut ε) a, hcS, hcI, hc0, ?_⟩
  have hnorm : ‖b‖ - ε < ‖a‖ := by
    have h := norm_sub_norm_le b a
    have h2' : ‖b - a‖ = ‖a - b‖ := norm_sub_rev _ _
    rw [h2'] at h
    linarith
  have hmem : ‖a‖ ∈ spectrum ℝ a := CStarAlgebra.norm_mem_spectrum_of_nonneg ha0
  have hcutpos : 0 < posCut ε ‖a‖ := posCut_pos (by rw [hεdef] at hnorm ⊢; linarith)
  intro hc
  have hspec : posCut ε ‖a‖ ∈ spectrum ℝ (cfc (posCut ε) a) := by
    rw [cfc_map_spectrum hasa hpc.continuousOn]
    exact ⟨‖a‖, hmem, rfl⟩
  rw [hc, spectrum.zero_eq] at hspec
  simp only [Set.mem_singleton_iff] at hspec
  exact absurd hspec (ne_of_gt hcutpos)

/-! ### Simplicity -/

/-- **Simplicity of a unital increasing union whose stages become full.**

If `B` is the closure of an increasing union of closed ⋆-subalgebras `S i`, and every nonzero
positive element of every stage is full in `B`, then every nonzero closed two-sided ideal of `B`
is all of `B`.

The fullness hypothesis is exactly what a later-stage point-evaluation summand supplies in an AH
tower: an element full in a later *stage* is a fortiori full in `B`, the same finite sums
witnessing it (`IsFullIn.isFull`). -/
theorem eq_top_of_stagewise_full [Nonempty ι] (hclosed : ∀ i, IsClosed (S i : Set B))
    (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    (hfull : ∀ (i : ι) (a : B), a ∈ S i → 0 ≤ a → a ≠ 0 → IsFull a)
    {I : Ideal B} [I.IsTwoSided] (hIclosed : IsClosed (I : Set B))
    {x : B} (hxI : x ∈ I) (hx : x ≠ 0) :
    I = ⊤ := by
  have hb0 : (0 : B) ≤ star x * x := star_mul_self_nonneg x
  have hbI : star x * x ∈ I := Ideal.mul_mem_left I _ hxI
  have hbne : star x * x ≠ 0 := (CStarRing.star_mul_self_ne_zero_iff x).mpr hx
  obtain ⟨j, -, c, hcS, hcI, hc0, hcne⟩ :=
    exists_ge_mem_ideal_of_nonneg hclosed hmono hdense hIclosed hbI hb0 hbne
      (Classical.arbitrary ι)
  exact (Ideal.eq_top_iff_one I).mpr (one_mem_of_isFull hIclosed hcI (hfull j c hcS hc0 hcne))

/-- **The simplicity theorem, in the form the endpoint consumes.**

`B` is the closure of an increasing union of closed ⋆-subalgebras `S i`, and every nonzero
positive element of a stage becomes full in some later stage.  Then `B` is a simple C⋆-algebra in
the sense of `IsSimpleCStar`: its only closed two-sided ideals are `⊥` and `⊤`.

The index `j` produced by `hfull` is not used — fullness in `S j` is fullness in `B` — but it is
what the tower actually supplies, so the hypothesis is stated in that form. -/
theorem isSimpleCStar_of_stagewise_full [Nonempty ι] (hclosed : ∀ i, IsClosed (S i : Set B))
    (hmono : Monotone S) (hdense : Dense (⋃ i, (S i : Set B)))
    (hfull : ∀ (i : ι) (a : B), a ∈ S i → 0 ≤ a → a ≠ 0 → ∃ j, i ≤ j ∧ IsFullIn (S j) a) :
    IsSimpleCStar B := by
  intro I hI hIclosed
  haveI := hI
  rcases eq_or_ne I ⊥ with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    obtain ⟨x, hxI, hx⟩ : ∃ x, x ∈ I ∧ x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact h ((Submodule.eq_bot_iff I).mpr fun x hxI => hcon x hxI)
    refine eq_top_of_stagewise_full hclosed hmono hdense ?_ hIclosed hxI hx
    intro i a haS ha0 hane
    obtain ⟨-, -, hfullin⟩ := hfull i a haS ha0 hane
    exact hfullin.isFull

end Ideal

end

end LIX

end GroupApproximation
