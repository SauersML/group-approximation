import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.TracialMatrixUltraproduct
import GroupApproximation.Analysis.UCPContractiveMatrix

/-!
# The local form of a quasidiagonal trace, and the passage to the sequence form

`Analysis.QuasidiagonalTrace` transcribes the conclusion of
Tikuisis--White--Winter as a *sequence*: matrix models `φₙ` whose
multiplicative and trace defects tend to zero.  That is the shape the rest of
this development consumes, because `ShulmanTrace.MFTraceModel` is a sequence
too.

**It is not the shape the theorem is proved in.**  Tikuisis--White--Winter,
*Quasidiagonality of nuclear C⋆-algebras*, Ann. of Math. (2) **185** (2017),
229--284, states and proves the conclusion in the *local* form: for every
finite `F ⊆ A` and every `ε > 0` there is **one** unital completely positive
`φ : A → M_k` with

```text
‖φ(xy) − φ(x)φ(y)‖ ≤ ε   and   |τ(x) − tr φ(x)| ≤ ε      for x, y ∈ F.
```

This file supplies that form and proves the two passages between them.  The
point is not cosmetic.  The two directions cost different things:

* **sequence ⟹ local** is free (`isLocallyQuasidiagonalTrace_of_isQuasidiagonalTrace`):
  finitely many null sequences are simultaneously small from some index on,
  which is `GroupApproximation.eventually_finset`.
* **local ⟹ sequence** is a diagonal argument
  (`isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`) and it consumes one
  thing the local form does not mention --- **separability** of `A`, to have a
  countable dense sequence to exhaust --- together with contractivity of unital
  completely positive maps, which is used to move a defect from a dense point
  to an arbitrary one and which is a **theorem** here
  (`Quasidiagonal.ucpContractive`, off the repository's own Stinespring
  dilation), not a hypothesis.

  It also needs `τ` to be continuous --- a defect controlled on a dense set
  says nothing off it otherwise --- and that is **not** a third hypothesis:
  `lipschitz_of_isLocallyQuasidiagonalTrace` derives it from the local form
  itself, since the models control `τ` at every point of `A` and not only on a
  dense subset.

So the local form is the *weaker* hypothesis, and it is the honest one to
assume from the literature: `Analysis.TikuisisWhiteWinterCore` takes it,
rather than the sequence form, and recovers the sequence form here.  Assuming
the sequence form directly would be assuming Tikuisis--White--Winter *and* the
diagonal argument, which is a theorem, not a citation.

## Why continuity of `τ` is not a hypothesis

`FaithfulTracialState` is algebraic --- a unital linear functional, positive
on `x⋆x` and tracial.  That such a functional on a C⋆-algebra is automatically
norm-decreasing is the standard fact `‖τ‖ = τ(1) = 1` for states, and it is
**not proved in this repository**: it needs the continuous functional calculus
to compare `τ(x)` with the spectral radius.

It is also not needed.  `lipschitz_of_isLocallyQuasidiagonalTrace` proves that
a locally quasidiagonal trace is `1`-Lipschitz **from the models**, using only
the ucp contraction bound: at the two-element set `{x, y}` the trace clause
pins `τ x` and `τ y` to within `ε` of two matrix traces whose difference is at
most `‖x − y‖`.  So no state-theoretic input enters this file, and since
`Quasidiagonal.ucpContractive` discharges the contraction bound outright,
**nothing in this file is conditional on anything.**

## What is proved here, unconditionally

Everything except the two named inputs it carries.  In particular
`norm_mul_defect_le` --- the estimate that moves a multiplicative defect from
a pair `(p, q)` to a nearby pair `(x, y)` --- is proved with no hypothesis
beyond contractivity of the single map involved, and it is the only estimate
the diagonal argument needs.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ## The local form -/

/-- **A locally quasidiagonal trace**: the finite-set/`ε` form of
`IsQuasidiagonalTrace`, and the form in which Tikuisis--White--Winter is
stated and proved.

For every finite `F ⊆ A` and every `ε > 0` there is a single unital completely
positive map into a matrix algebra whose multiplicative defect on `F × F` and
whose trace defect on `F` are both at most `ε`.

Nothing is asked *between* different `F`'s: the maps for different finite sets
are unrelated, and their matrix sizes are unrelated.  That is what makes this
weaker than `IsQuasidiagonalTrace`, and it is why recovering the sequence form
needs a countable exhaustion of `A`. -/
def IsLocallyQuasidiagonalTrace (τ : A → ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ x ∈ F, ∀ y ∈ F, ‖φ (x * y) - φ x * φ y‖ ≤ ε) ∧
      (∀ x ∈ F, ‖τ x - normTrace Y (φ x)‖ ≤ ε)

/-- **The local form read along a sequence.**  Applying
`IsLocallyQuasidiagonalTrace` at the finite set `{u 0, …, u m}` gives the
same data indexed by natural numbers `≤ m`, which is the shape the diagonal
argument below wants: it never needs to know that the `u i` are distinct, and
it never needs a `DecidableEq` instance on `A` in a statement.

The `Finset` lives only inside the proof, where `classical` supplies the
decidability that `Finset.image` needs. -/
theorem IsLocallyQuasidiagonalTrace.seq {τ : A → ℂ}
    (h : IsLocallyQuasidiagonalTrace τ) (u : ℕ → A) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ i ≤ m, ∀ j ≤ m, ‖φ (u i * u j) - φ (u i) * φ (u j)‖ ≤ ε) ∧
      (∀ i ≤ m, ‖τ (u i) - normTrace Y (φ (u i))‖ ≤ ε) := by
  classical
  obtain ⟨Y, φ, h1, hcp, hmul, htr⟩ := h ((Finset.range (m + 1)).image u) ε hε
  have hmem : ∀ i ≤ m, u i ∈ (Finset.range (m + 1)).image u := fun i hi ↦
    Finset.mem_image_of_mem u (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact ⟨Y, φ, h1, hcp, fun i hi j hj ↦ hmul _ (hmem i hi) _ (hmem j hj),
    fun i hi ↦ htr _ (hmem i hi)⟩

/-! ## The free direction -/

/-- **A quasidiagonal trace is locally quasidiagonal.**  Only the models far
enough along the sequence are used: the `|F|²` multiplicative defects and the
`|F|` trace defects are finitely many null sequences, so one index makes all of
them at most `ε`.

This is the direction that needs nothing --- no separability, no contractivity,
no continuity of `τ`. -/
theorem isLocallyQuasidiagonalTrace_of_isQuasidiagonalTrace {τ : A → ℂ}
    (h : IsQuasidiagonalTrace τ) : IsLocallyQuasidiagonalTrace τ := by
  obtain ⟨M⟩ := h
  intro F ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_finset (F ×ˢ F)
    (fun p n ↦ ‖M.map n (p.1 * p.2) - M.map n p.1 * M.map n p.2‖ ≤ ε)
    (by
      intro p _
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (TracialUltraproduct.eventually_lt_of_tendsto_zero
          (M.tendsto_mul p.1 p.2) hε)
      exact ⟨N, fun n hn ↦ (hN n hn).le⟩)
  obtain ⟨N₂, hN₂⟩ := eventually_finset F
    (fun x n ↦ ‖τ x - normTrace (M.space n) (M.map n x)‖ ≤ ε)
    (by
      intro x _
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (TracialUltraproduct.eventually_lt_of_tendsto_zero
          (M.tendsto_trace x) hε)
      exact ⟨N, fun n hn ↦ (hN n hn).le⟩)
  refine ⟨M.space (max N₁ N₂), M.map (max N₁ N₂), M.map_one _,
    M.completelyPositive _, ?_, ?_⟩
  · intro x hx y hy
    exact hN₁ (max N₁ N₂) (le_max_left _ _) (x, y)
      (Finset.mem_product.mpr ⟨hx, hy⟩)
  · intro x hx
    exact hN₂ (max N₁ N₂) (le_max_right _ _) x hx

/-! ## The local form already forces `τ` to be continuous -/

/-- **A locally quasidiagonal trace is `1`-Lipschitz**, over the ucp facts and
nothing else.

At the two-element set `{x, y}` and tolerance `ε` the local form supplies one
ucp `φ` with `|τ x − tr φ x| ≤ ε` and `|τ y − tr φ y| ≤ ε`, and

```text
τ x − τ y = (τ x − tr φ x) + tr φ (x − y) − (τ y − tr φ y),
```

whose middle term is at most `‖φ (x − y)‖ ≤ ‖x − y‖`.  Letting `ε → 0` gives
the bound with constant exactly `1`.

This is worth isolating because it removes a hypothesis that the obvious
formulation of the diagonal argument carries.  Continuity of `τ` is genuinely
needed there --- a defect controlled on a dense set says nothing off it
otherwise --- but it does **not** have to be assumed: the models control `τ`
at every point of `A`, not only on a dense subset, so they force it
themselves.  A tracial state on a C⋆-algebra is `1`-Lipschitz anyway, by
`‖τ‖ = τ(1) = 1`; that standard fact is not proved in this repository and is
not needed. -/
theorem lipschitz_of_isLocallyQuasidiagonalTrace
    {τ : A → ℂ} (h : IsLocallyQuasidiagonalTrace τ) (x y : A) :
    ‖τ x - τ y‖ ≤ ‖x - y‖ := by
  classical
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨Y, φ, hone, hcp, _, htr⟩ := h {x, y} (ε / 2) (by linarith)
  have hx : ‖τ x - normTrace Y (φ x)‖ ≤ ε / 2 :=
    htr x (Finset.mem_insert_self x {y})
  have hy : ‖τ y - normTrace Y (φ y)‖ ≤ ε / 2 :=
    htr y (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  have hmid : ‖normTrace Y (φ x) - normTrace Y (φ y)‖ ≤ ‖x - y‖ := by
    rw [← normTrace_sub, ← map_sub]
    exact (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm Y
      (φ (x - y))).trans
      (ucpContractive.norm_le A inferInstance Y φ hone hcp (x - y))
  have e : τ x - τ y
      = (τ x - normTrace Y (φ x)) + (normTrace Y (φ x) - normTrace Y (φ y))
        - (τ y - normTrace Y (φ y)) := by ring
  rw [e]
  have s1 := norm_sub_le ((τ x - normTrace Y (φ x))
    + (normTrace Y (φ x) - normTrace Y (φ y))) (τ y - normTrace Y (φ y))
  have s2 := norm_add_le (τ x - normTrace Y (φ x))
    (normTrace Y (φ x) - normTrace Y (φ y))
  linarith [s1, s2, hx, hy, hmid]

/-! ## The estimate that moves a defect to a nearby pair -/

/-- **Transporting a multiplicative defect along the norm.**  If `φ` is
contractive and its multiplicative defect at the pair `(p, q)` is at most `η`,
then its defect at any pair `(x, y)` is controlled by `η` and by how far
`(x, y)` is from `(p, q)`:

```text
‖φ(xy) − φ(x)φ(y)‖ ≤ ‖xy − pq‖ + η + (‖p‖‖q − y‖ + ‖p − x‖‖y‖).
```

The proof is the three-term split

```text
φ(xy) − φ(x)φ(y) = (φ(xy) − φ(pq)) + (φ(pq) − φ(p)φ(q))
                     + (φ(p)(φ(q) − φ(y)) + (φ(p) − φ(x))φ(y)),
```

each summand estimated by contractivity and submultiplicativity of the matrix
operator norm.  No positivity, unitality or linearity of `φ` beyond additivity
is used --- contractivity is the whole input, which is why the diagonal
argument below pays for `UCPContractive` exactly once. -/
theorem norm_mul_defect_le {Y : FiniteModel} (φ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (hcontr : ∀ z : A, ‖φ z‖ ≤ ‖z‖) (x y p q : A) {η : ℝ}
    (hpq : ‖φ (p * q) - φ p * φ q‖ ≤ η) :
    ‖φ (x * y) - φ x * φ y‖
      ≤ ‖x * y - p * q‖ + η + (‖p‖ * ‖q - y‖ + ‖p - x‖ * ‖y‖) := by
  have e : φ (x * y) - φ x * φ y
      = (φ (x * y) - φ (p * q)) + (φ (p * q) - φ p * φ q)
        + (φ p * (φ q - φ y) + (φ p - φ x) * φ y) := by
    simp only [mul_sub, sub_mul]
    abel
  have h1 : ‖φ (x * y) - φ (p * q)‖ ≤ ‖x * y - p * q‖ := by
    rw [← map_sub]
    exact hcontr _
  have h3 : ‖φ p * (φ q - φ y)‖ ≤ ‖p‖ * ‖q - y‖ := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    refine mul_le_mul (hcontr p) ?_ (norm_nonneg _) (norm_nonneg _)
    rw [← map_sub]
    exact hcontr _
  have h4 : ‖(φ p - φ x) * φ y‖ ≤ ‖p - x‖ * ‖y‖ := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    refine mul_le_mul ?_ (hcontr y) (norm_nonneg _) (norm_nonneg _)
    rw [← map_sub]
    exact hcontr _
  calc ‖φ (x * y) - φ x * φ y‖
      = ‖(φ (x * y) - φ (p * q)) + (φ (p * q) - φ p * φ q)
          + (φ p * (φ q - φ y) + (φ p - φ x) * φ y)‖ := by rw [e]
    _ ≤ ‖(φ (x * y) - φ (p * q)) + (φ (p * q) - φ p * φ q)‖
          + ‖φ p * (φ q - φ y) + (φ p - φ x) * φ y‖ := norm_add_le _ _
    _ ≤ ‖φ (x * y) - φ (p * q)‖ + ‖φ (p * q) - φ p * φ q‖
          + (‖φ p * (φ q - φ y)‖ + ‖(φ p - φ x) * φ y‖) :=
        add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ ‖x * y - p * q‖ + η + (‖p‖ * ‖q - y‖ + ‖p - x‖ * ‖y‖) :=
        add_le_add (add_le_add h1 hpq) (add_le_add h3 h4)

/-- The product estimate in the algebra itself: `xy` is close to `pq` when `x`
is close to `p` and `y` is close to `q`. -/
theorem norm_mul_sub_mul_le (x y p q : A) :
    ‖x * y - p * q‖ ≤ ‖x‖ * ‖y - q‖ + ‖x - p‖ * ‖q‖ := by
  have e : x * y - p * q = x * (y - q) + (x - p) * q := by
    simp only [mul_sub, sub_mul]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-- A point of `A` is within `δ` of a nearby point in norm, read as a bound on
its own norm.  Used to keep the constants of the diagonal argument explicit. -/
theorem norm_le_of_norm_sub_le {x p : A} {δ : ℝ} (h : ‖p - x‖ ≤ δ) :
    ‖p‖ ≤ ‖x‖ + δ := by
  have e : p = x + (p - x) := by abel
  calc ‖p‖ = ‖x + (p - x)‖ := by rw [← e]
    _ ≤ ‖x‖ + ‖p - x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + δ := by linarith

/-- **A scale small enough for a fixed constant.**  Given `K > 0` and
`ε > 0` there is a `δ ∈ (0, 1]` with `K δ ≤ ε`.  Stated separately so that the
diagonal argument below never manipulates a quotient inside an estimate. -/
theorem exists_small_scale (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ K * δ ≤ ε := by
  have hKne : K ≠ 0 := ne_of_gt hK
  refine ⟨min 1 (ε / K), lt_min one_pos (div_pos hε hK), min_le_left _ _, ?_⟩
  have h1 : min 1 (ε / K) ≤ ε / K := min_le_right _ _
  have h2 : K * (ε / K) = ε := by field_simp
  linarith [mul_le_mul_of_nonneg_left h1 hK.le, h2]

/-! ## The diagonal argument -/

/-- **The local form gives the sequence form on a separable algebra.**

Exhaust `A` by a dense sequence `u`, take the model `φₙ` that the local form
supplies for `{u 0, …, u n}` at tolerance `1/(n+1)`, and check the two
sequence clauses at an arbitrary pair of elements by moving to nearby points
of the dense sequence.  Both moves cost a contraction estimate:
`norm_mul_defect_le` on the multiplicative clause and
`PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm` on the trace clause.

**Separability is the only premise beyond the local form.**  Two other facts
are used and neither is assumed: `‖φₙ z‖ ≤ ‖z‖` is `ucpContractive`, and
`1`-Lipschitz continuity of `τ` --- needed because a defect controlled on a
dense set says nothing off it --- is
`lipschitz_of_isLocallyQuasidiagonalTrace`, which reads it off the models.

Separability is a property of the ambient algebra, not of the trace.  In
particular this theorem does **not** assume any part of
Tikuisis--White--Winter. -/
theorem isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace {τ : A → ℂ}
    (hsep : TopologicalSpace.SeparableSpace A)
    (h : IsLocallyQuasidiagonalTrace τ) :
    IsQuasidiagonalTrace τ := by
  classical
  have hτ : ∀ x y : A, ‖τ x - τ y‖ ≤ ‖x - y‖ :=
    lipschitz_of_isLocallyQuasidiagonalTrace h
  haveI := hsep
  haveI : Nonempty A := ⟨1⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq A
  have hchoice : ∀ n : ℕ, ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ i ≤ n, ∀ j ≤ n,
        ‖φ (u i * u j) - φ (u i) * φ (u j)‖ ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ i ≤ n, ‖τ (u i) - normTrace Y (φ (u i))‖ ≤ 1 / ((n : ℝ) + 1)) :=
    fun n ↦ h.seq u n (by positivity)
  choose Y φ hone hcp hmul htr using hchoice
  have hcontr : ∀ (n : ℕ) (z : A), ‖φ n z‖ ≤ ‖z‖ := fun n z ↦
    ucpContractive.norm_le A inferInstance (Y n) (φ n) (hone n) (hcp n) z
  have hdiv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    fun ε hε ↦ TracialUltraproduct.eventually_lt_of_tendsto_zero
      tendsto_one_div_add_atTop_nhds_zero_nat hε
  refine ⟨{ space := Y, map := φ, map_one := hone, completelyPositive := hcp
            tendsto_mul := ?_
            tendsto_trace := ?_ }⟩
  · -- the multiplicative clause
    intro a b
    refine TracialUltraproduct.tendsto_zero_of_forall_eventually_lt
      (fun n ↦ norm_nonneg _) ?_
    intro ε hε
    obtain ⟨δ, hδ0, hδ1, hδK⟩ := exists_small_scale
      (2 * ‖a‖ + 2 * ‖b‖ + 2) (ε / 2) (by positivity) (by linarith)
    obtain ⟨i, hi⟩ := hu.exists_dist_lt a hδ0
    obtain ⟨j, hj⟩ := hu.exists_dist_lt b hδ0
    rw [dist_eq_norm] at hi hj
    filter_upwards [hdiv (ε / 2) (by linarith), Filter.eventually_ge_atTop i,
      Filter.eventually_ge_atTop j] with n hn hni hnj
    have hai : ‖a - u i‖ ≤ δ := hi.le
    have hbj : ‖b - u j‖ ≤ δ := hj.le
    have hia : ‖u i - a‖ ≤ δ := by rw [norm_sub_rev]; exact hi.le
    have hjb : ‖u j - b‖ ≤ δ := by rw [norm_sub_rev]; exact hj.le
    have hui : ‖u i‖ ≤ ‖a‖ + 1 :=
      (norm_le_of_norm_sub_le hia).trans (by linarith)
    have huj : ‖u j‖ ≤ ‖b‖ + 1 :=
      (norm_le_of_norm_sub_le hjb).trans (by linarith)
    have hkey := norm_mul_defect_le (φ n) (hcontr n) a b (u i) (u j)
      (hmul n i hni j hnj)
    have hprod : ‖a * b - u i * u j‖ ≤ ‖a‖ * δ + δ * (‖b‖ + 1) := by
      refine (norm_mul_sub_mul_le a b (u i) (u j)).trans ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hbj (norm_nonneg a))
        (mul_le_mul hai huj (norm_nonneg _) hδ0.le)
    have hlast : ‖u i‖ * ‖u j - b‖ + ‖u i - a‖ * ‖b‖
        ≤ (‖a‖ + 1) * δ + δ * ‖b‖ :=
      add_le_add (mul_le_mul hui hjb (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right hia (norm_nonneg b))
    linarith [hkey, hprod, hlast, hδK, hn]
  · -- the trace clause
    intro a
    refine TracialUltraproduct.tendsto_zero_of_forall_eventually_lt
      (fun n ↦ norm_nonneg _) ?_
    intro ε hε
    obtain ⟨i, hi⟩ := hu.exists_dist_lt a (show (0 : ℝ) < ε / 4 by linarith)
    rw [dist_eq_norm] at hi
    filter_upwards [hdiv (ε / 2) (by linarith), Filter.eventually_ge_atTop i]
      with n hn hni
    have h1 : ‖τ a - τ (u i)‖ ≤ ‖a - u i‖ := hτ a (u i)
    have h2 : ‖τ (u i) - normTrace (Y n) (φ n (u i))‖ ≤ 1 / ((n : ℝ) + 1) :=
      htr n i hni
    have h3 : ‖normTrace (Y n) (φ n (u i)) - normTrace (Y n) (φ n a)‖
        ≤ ‖a - u i‖ := by
      rw [← normTrace_sub, ← map_sub]
      exact (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm (Y n)
        (φ n (u i - a))).trans
        ((hcontr n (u i - a)).trans (le_of_eq (norm_sub_rev (u i) a)))
    have e : τ a - normTrace (Y n) (φ n a)
        = (τ a - τ (u i)) + (τ (u i) - normTrace (Y n) (φ n (u i)))
          + (normTrace (Y n) (φ n (u i)) - normTrace (Y n) (φ n a)) := by
      ring
    have e1 := norm_add_le ((τ a - τ (u i))
      + (τ (u i) - normTrace (Y n) (φ n (u i))))
      (normTrace (Y n) (φ n (u i)) - normTrace (Y n) (φ n a))
    have e2 := norm_add_le (τ a - τ (u i))
      (τ (u i) - normTrace (Y n) (φ n (u i)))
    rw [e]
    linarith [e1, e2, h1, h2, h3, hi, hn]

/-! ## Checking the local form on a dense subset -/

/-- **It is enough to test the local form on a dense subset.**

Every proof of a quasidiagonality statement begins here: one does not verify
the two defects at arbitrary elements of `A`, but at a dense `⋆`-subalgebra
--- for a group C⋆-algebra, at finitely many group elements --- and lets the
estimates propagate.  This theorem is that propagation, and it is proved with
the same two estimates the diagonal argument uses: `norm_mul_defect_le` moves
a multiplicative defect from `(d x, d y)` to `(x, y)`, and contractivity of
`φ` moves a trace defect.

The tolerance bookkeeping is explicit.  With `C = ∑_{x ∈ F} ‖x‖` a crude
uniform bound on `F` and `δ ≤ 1` chosen so that `(4C + 2) δ ≤ ε/2`, the four
error terms of `norm_mul_defect_le` sum to at most `(4C + 2) δ`, and the trace
clause picks up `2δ`.

`hτ` --- that `τ` is `1`-Lipschitz --- **is** a hypothesis here, unlike in
`isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`, and the difference is
not an oversight.  There, `lipschitz_of_isLocallyQuasidiagonalTrace` derives
it, because the hypothesis controls `τ` at *every* point of `A`.  Here the
hypothesis controls `τ` only on `D`, which pins `τ` down on `D` and says
nothing off it; a functional agreeing with a quasidiagonal trace on a dense
set and wild elsewhere would satisfy everything but the conclusion.  For the
intended `τ` --- a tracial state --- the premise is the standard
`‖τ‖ = τ(1) = 1`, which this repository does not prove and which is therefore
visible in the type. -/
theorem isLocallyQuasidiagonalTrace_of_dense {τ : A → ℂ} {D : Set A}
    (hD : Dense D) (hτ : ∀ x y : A, ‖τ x - τ y‖ ≤ ‖x - y‖)
    (h : ∀ (G : Finset A), ↑G ⊆ D → ∀ η : ℝ, 0 < η →
      ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
        φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
        (∀ x ∈ G, ∀ y ∈ G, ‖φ (x * y) - φ x * φ y‖ ≤ η) ∧
        (∀ x ∈ G, ‖τ x - normTrace Y (φ x)‖ ≤ η)) :
    IsLocallyQuasidiagonalTrace τ := by
  classical
  intro F ε hε
  have hCnn : (0 : ℝ) ≤ ∑ z ∈ F, ‖z‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hbd : ∀ z ∈ F, ‖z‖ ≤ ∑ w ∈ F, ‖w‖ := fun z hz ↦
    Finset.single_le_sum (f := fun w : A ↦ ‖w‖) (fun _ _ ↦ norm_nonneg _) hz
  obtain ⟨δ, hδ0, hδ1, hδC⟩ := exists_small_scale
    (4 * (∑ z ∈ F, ‖z‖) + 2) (ε / 2) (by positivity) (by linarith)
  have hchoice : ∀ x : A, ∃ y : A, y ∈ D ∧ ‖x - y‖ ≤ δ := by
    intro x
    obtain ⟨y, hyD, hy⟩ := hD.exists_dist_lt x hδ0
    refine ⟨y, hyD, ?_⟩
    rw [← dist_eq_norm]
    exact hy.le
  choose d hdD hdclose using hchoice
  have hsub : ↑(F.image d) ⊆ D := by
    intro z hz
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
    obtain ⟨x, _, rfl⟩ := hz
    exact hdD x
  obtain ⟨Y, φ, hone, hcp, hmul, htr⟩ := h (F.image d) hsub (ε / 2) (by linarith)
  have hcontr : ∀ z : A, ‖φ z‖ ≤ ‖z‖ := fun z ↦
    ucpContractive.norm_le A inferInstance Y φ hone hcp z
  refine ⟨Y, φ, hone, hcp, ?_, ?_⟩
  · intro x hx y hy
    have hdx : d x ∈ F.image d := Finset.mem_image_of_mem d hx
    have hdy : d y ∈ F.image d := Finset.mem_image_of_mem d hy
    have hxC : ‖x‖ ≤ ∑ z ∈ F, ‖z‖ := hbd x hx
    have hyC : ‖y‖ ≤ ∑ z ∈ F, ‖z‖ := hbd y hy
    have hdxx : ‖d x - x‖ ≤ δ := by
      rw [norm_sub_rev]; exact hdclose x
    have hdyy : ‖d y - y‖ ≤ δ := by
      rw [norm_sub_rev]; exact hdclose y
    have hdxn : ‖d x‖ ≤ (∑ z ∈ F, ‖z‖) + 1 :=
      (norm_le_of_norm_sub_le hdxx).trans (by linarith)
    have hdyn : ‖d y‖ ≤ (∑ z ∈ F, ‖z‖) + 1 :=
      (norm_le_of_norm_sub_le hdyy).trans (by linarith)
    have hkey := norm_mul_defect_le φ hcontr x y (d x) (d y)
      (hmul _ hdx _ hdy)
    have hprod : ‖x * y - d x * d y‖
        ≤ (∑ z ∈ F, ‖z‖) * δ + δ * ((∑ z ∈ F, ‖z‖) + 1) := by
      refine (norm_mul_sub_mul_le x y (d x) (d y)).trans ?_
      exact add_le_add
        (mul_le_mul hxC (hdclose y) (norm_nonneg _) hCnn)
        (mul_le_mul (hdclose x) hdyn (norm_nonneg _) hδ0.le)
    have hlast : ‖d x‖ * ‖d y - y‖ + ‖d x - x‖ * ‖y‖
        ≤ ((∑ z ∈ F, ‖z‖) + 1) * δ + δ * (∑ z ∈ F, ‖z‖) :=
      add_le_add (mul_le_mul hdxn hdyy (norm_nonneg _) (by positivity))
        (mul_le_mul hdxx hyC (norm_nonneg _) hδ0.le)
    linarith [hkey, hprod, hlast, hδC]
  · intro x hx
    have hdx : d x ∈ F.image d := Finset.mem_image_of_mem d hx
    have hdxx : ‖d x - x‖ ≤ δ := by
      rw [norm_sub_rev]; exact hdclose x
    have h1 : ‖τ x - τ (d x)‖ ≤ δ := (hτ x (d x)).trans (hdclose x)
    have h2 : ‖τ (d x) - normTrace Y (φ (d x))‖ ≤ ε / 2 := htr _ hdx
    have h3 : ‖normTrace Y (φ (d x)) - normTrace Y (φ x)‖ ≤ δ := by
      rw [← normTrace_sub, ← map_sub]
      refine (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm Y
        (φ (d x - x))).trans ?_
      exact (hcontr (d x - x)).trans hdxx
    have e : τ x - normTrace Y (φ x)
        = (τ x - τ (d x)) + (τ (d x) - normTrace Y (φ (d x)))
          + (normTrace Y (φ (d x)) - normTrace Y (φ x)) := by ring
    have s1 := norm_add_le ((τ x - τ (d x))
      + (τ (d x) - normTrace Y (φ (d x))))
      (normTrace Y (φ (d x)) - normTrace Y (φ x))
    have s2 := norm_add_le (τ x - τ (d x))
      (τ (d x) - normTrace Y (φ (d x)))
    have hCδ : 0 ≤ (∑ z ∈ F, ‖z‖) * δ := mul_nonneg hCnn hδ0.le
    rw [e]
    linarith [s1, s2, h1, h2, h3, hδC, hCδ]

/-! ## The two forms agree on a separable algebra -/

/-- **The two transcriptions are equivalent** on a separable algebra with a
continuous trace, over `UCPContractive`.  The right-to-left direction is the
diagonal argument; the left-to-right direction is free.

This is the statement that makes it legitimate for
`Analysis.TikuisisWhiteWinterCore` to assume the local form and for the rest
of the development to consume the sequence form. -/
theorem isQuasidiagonalTrace_iff_isLocallyQuasidiagonalTrace {τ : A → ℂ}
    (hsep : TopologicalSpace.SeparableSpace A) :
    IsQuasidiagonalTrace τ ↔ IsLocallyQuasidiagonalTrace τ :=
  ⟨isLocallyQuasidiagonalTrace_of_isQuasidiagonalTrace,
    isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace hsep⟩

end

end Quasidiagonal
end GroupApproximation
