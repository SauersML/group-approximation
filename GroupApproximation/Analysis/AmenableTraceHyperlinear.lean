import GroupApproximation.Analysis.HilbertSchmidtPolarCorrection
import GroupApproximation.Analysis.MaximalCStarKazhdanAverage
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Sofic.HyperlinearAmplification
import GroupApproximation.Sofic.LeavittTraceFloor

/-!
# An amenable canonical trace makes the group hyperlinear

Brown, *Invariant means and finite representation theory of C⋆-algebras*,
Mem. Amer. Math. Soc. **184** (2006), no. 865, Theorem 3.1.7 `(1) ⟹ (2)`: an
amenable trace on a unital C⋆-algebra embeds the associated finite von Neumann
algebra into `R^ω`.  At the canonical trace of `C⋆(G)` --- amenable exactly when
`G` has Kirchberg's factorization property, Brown's Theorem 4.1.9 --- that says
`L(G)` embeds in `R^ω`, which is hyperlinearity of `G`.

`isHyperlinear_of_isAmenableTrace_canonicalMaximal` is that implication, proved
rather than cited.  It is what
`Manuscript/NinetyNineProblems/FactorizationImpliesHyperlinear.lean` names
`BrownAmenableTraceHyperlinearInput` and consumes as an assumed input.

## Why it is provable here

`IsHyperlinear` (`Sofic/Hyperlinear.lean`) asks, for every finite `F ⊆ G` and
every `ε > 0`, for **genuinely unitary** matrices `u(g)` whose multiplicative
defect and whose mutual separation are controlled in the *normalized
Hilbert--Schmidt* metric `hsDistSq`:

* `hsDistSq (u (g*h)) (u g * u h) ≤ ε`, and
* `2 - ε ≤ hsDistSq (u g) (u h)` for `g ≠ h`.

Both clauses are Hilbert--Schmidt, not operator-norm, which is why an amenable
trace suffices --- its models are approximately multiplicative in the `2`-norm
only.  The one thing the definition does not negotiate is unitarity, and that
is supplied by `HilbertSchmidtPolar.exists_unitary_hsNorm_sub_le`: every square
matrix `x` lies within `‖x⋆x − 1‖₂` of a unitary.

## The four estimates

Write `xₙ(g) := φₙ(u_g)` for the u.c.p. models of the trace at the canonical
generators.  Everything rests on four limits, each proved once and then
quantified over the finite test set:

1. `tendsto_hsNorm_gram`: `‖xₙ(g)⋆xₙ(g) − 1‖₂ → 0`.  The models preserve
   adjoints (`Quasidiagonal.ucp_map_star`), so `xₙ(g)⋆ = xₙ(g⁻¹)`, and the Gram
   defect is the multiplicative defect at the pair `(u_{g⁻¹}, u_g)`, whose
   product is the unit.
2. `tendsto_hsNorm_mul`: `‖xₙ(gh) − xₙ(g)xₙ(h)‖₂ → 0`, which is
   `AmenableTraceModel.tendsto_mul_hs` at a pair of generators.
3. `tendsto_norm_normTrace_mul_conjTranspose`: for `g ≠ h`,
   `|tr xₙ(g)xₙ(h)⋆| → 0`.  The product is asymptotically `xₙ(gh⁻¹)`, whose
   normalized trace converges to `τ(u_{gh⁻¹}) = 0` --- the canonical trace is
   the `δ`-function on the group, and this is the only step that uses the
   *canonical* trace rather than an arbitrary amenable one.
4. `eventually_card_pos`: the models are eventually nonempty, because an empty
   model reports normalized trace `0` while the trace clause at the unit forces
   that quantity near `1`.

Then `δ := min 1 (ε / 22)`, one index `n` is chosen making all of them small
simultaneously on `F` (`Filter.eventually_all_finset`), each `xₙ(g)` is
polar-corrected to a unitary `u(g)`, and the two clauses follow by triangle
inequalities.

## Constants, and why they are not tracked

The additive estimate used throughout is `hsNormSq_add_le`,
`‖A+B‖₂² ≤ 2‖A‖₂² + 2‖B‖₂²` --- a factor `2` per step rather than the sharp
triangle inequality, which the repository does not carry for `hsNorm`.  The
multiplicative clause splits into three terms and so pays `22δ²`; the
separation clause pays `3δ`.  Neither constant matters: `ε` is universally
quantified and `δ` is chosen after it.  Nothing here would improve if the sharp
inequality were available.

The separation constant, by contrast, **is** sharp, and it is not reached by
amplification: `hsDistSq_of_unitary` turns it into a statement about
`Re tr(u(g)u(h)⋆)`, and the canonical trace vanishes identically off the
identity, so the estimate lands at `2 - ε` directly.

## What is not proved

No countability hypothesis is used or needed.  Nothing here proves a converse:
hyperlinearity does not imply the factorization property (Thom, Groups Geom.
Dyn. **4** (2010), 195--208), which
`Manuscript/NinetyNineProblems/FactorizationProperty.lean` records.
-/

namespace GroupApproximation

namespace AmenableTraceHyperlinear

open Filter Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## Hilbert--Schmidt toolbox -/

section Toolbox

variable (Y : FiniteModel)

/-- The normalized squared Hilbert--Schmidt norm is symmetric in a difference.

The invariance of the norm under negation is taken as a local `have` rather
than through the repository's standalone lemma for it, which lives in
`Sofic/UltraproductKazhdanTransport.lean` and would pull the Kazhdan transport
module into the dependencies of this one.  That is the same trade
`ConsistencyDistance.sdDistSq_comm` makes, for the same reason, and its comment
records it: the line is cheaper than the dependency, and the audit's duplicate
scan reads declarations rather than `have`s. -/
theorem hsNormSq_sub_comm (A B : Matrix Y Y ℂ) :
    hsNormSq Y (A - B) = hsNormSq Y (B - A) := by
  have hneg : ∀ X : Matrix Y Y ℂ, hsNormSq Y (-X) = hsNormSq Y X := by
    intro X
    simp [hsNormSq]
  rw [← hneg (B - A), neg_sub]

/-- The same, at the unsquared norm. -/
theorem hsNorm_sub_comm (A B : Matrix Y Y ℂ) :
    hsNorm Y (A - B) = hsNorm Y (B - A) := by
  unfold hsNorm
  rw [hsNormSq_sub_comm]

/-- Adjoints do not move the normalized Hilbert--Schmidt norm. -/
theorem hsNorm_conjTranspose (A : Matrix Y Y ℂ) : hsNorm Y Aᴴ = hsNorm Y A := by
  unfold hsNorm
  rw [hsNormSq_conjTranspose]

/-- Submultiplicativity against the operator norm of the left factor. -/
theorem hsNorm_mul_le_left (A B : Matrix Y Y ℂ) :
    hsNorm Y (A * B) ≤ ‖A‖ * hsNorm Y B := by
  unfold hsNorm
  have h := Real.sqrt_le_sqrt (hsNormSq_mul_le_sq_l2_opNorm_mul Y A B)
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg A)] at h

/-- Submultiplicativity against the operator norm of the right factor. -/
theorem hsNorm_mul_le_right (A B : Matrix Y Y ℂ) :
    hsNorm Y (A * B) ≤ ‖B‖ * hsNorm Y A := by
  unfold hsNorm
  have h := Real.sqrt_le_sqrt (hsNormSq_mul_le_sq_l2_opNorm_right Y A B)
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg B)] at h

/-- Passing from the norm to its square. -/
theorem hsNormSq_le_sq_of_hsNorm_le {A : Matrix Y Y ℂ} {c : ℝ}
    (h : hsNorm Y A ≤ c) : hsNormSq Y A ≤ c ^ 2 := by
  have hsq : hsNormSq Y A = hsNorm Y A ^ 2 := by
    unfold hsNorm
    rw [Real.sq_sqrt (hsNormSq_nonneg Y A)]
  rw [hsq]
  exact pow_le_pow_left₀ (hsNorm_nonneg Y A) h 2

/-- Passing back from the square to the norm. -/
theorem hsNorm_le_of_hsNormSq_le {A : Matrix Y Y ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : hsNormSq Y A ≤ c ^ 2) : hsNorm Y A ≤ c := by
  unfold hsNorm
  have hle := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq hc] at hle

/-- The hyperlinear distance is the squared norm of the difference. -/
theorem hsDistSq_eq_hsNormSq_sub (A B : Matrix Y Y ℂ) :
    hsDistSq Y A B = hsNormSq Y (A - B) := by
  simp [hsDistSq, hsNormSq]

/-- **The product estimate.**  Replacing both factors of a product by
Hilbert--Schmidt neighbours costs `4δ²`, provided the two factors that survive
the splitting `xy - uw = (x-u)y + u(y-w)` are contractions. -/
theorem hsNormSq_mul_sub_mul_le {x y v w : Matrix Y Y ℂ} {δ : ℝ}
    (hy : ‖y‖ ≤ 1) (hv : ‖v‖ ≤ 1) (h1 : hsNorm Y (v - x) ≤ δ)
    (h2 : hsNorm Y (w - y) ≤ δ) :
    hsNormSq Y (x * y - v * w) ≤ 4 * δ ^ 2 := by
  have hx : hsNormSq Y (x - v) ≤ δ ^ 2 := by
    rw [hsNormSq_sub_comm]
    exact hsNormSq_le_sq_of_hsNorm_le Y h1
  have hw : hsNormSq Y (y - w) ≤ δ ^ 2 := by
    rw [hsNormSq_sub_comm]
    exact hsNormSq_le_sq_of_hsNorm_le Y h2
  have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  have hv2 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
  have hleft : hsNormSq Y ((x - v) * y) ≤ δ ^ 2 := by
    refine le_trans (hsNormSq_mul_le_sq_l2_opNorm_right Y (x - v) y) ?_
    calc ‖y‖ ^ 2 * hsNormSq Y (x - v)
        ≤ 1 * hsNormSq Y (x - v) :=
          mul_le_mul_of_nonneg_right hy2 (hsNormSq_nonneg Y (x - v))
      _ = hsNormSq Y (x - v) := one_mul _
      _ ≤ δ ^ 2 := hx
  have hright : hsNormSq Y (v * (y - w)) ≤ δ ^ 2 := by
    refine le_trans (hsNormSq_mul_le_sq_l2_opNorm_mul Y v (y - w)) ?_
    calc ‖v‖ ^ 2 * hsNormSq Y (y - w)
        ≤ 1 * hsNormSq Y (y - w) :=
          mul_le_mul_of_nonneg_right hv2 (hsNormSq_nonneg Y (y - w))
      _ = hsNormSq Y (y - w) := one_mul _
      _ ≤ δ ^ 2 := hw
  have hsplit : x * y - v * w = (x - v) * y + v * (y - w) := by noncomm_ring
  rw [hsplit]
  have hadd := hsNormSq_add_le Y ((x - v) * y) (v * (y - w))
  linarith

end Toolbox

/-! ## The canonical generator at the identity -/

section Model

variable {G : Type u} [Group G]

/-- The canonical generator of the identity is the unit.  This is the clause of
the generator calculus of `Analysis/MaximalCStarKazhdanAverage.lean` that is
left implicit there; the proof is the same `congrArg` on the unitary group. -/
theorem maximalGroupCStarGenerator_one :
    maximalGroupCStarGenerator G 1 = 1 :=
  congrArg (fun w : unitary (MaximalGroupCStar G) ↦ (w : MaximalGroupCStar G))
    (map_one (maximalGroupCStarUnitaryHom G))

/-! ## The model matrices -/

variable (M : Quasidiagonal.AmenableTraceModel
  (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a))

/-- The matrix model of a group element: the u.c.p. model of the trace,
evaluated at the canonical generator. -/
def modelMatrix (n : ℕ) (g : G) : Matrix (M.space n) (M.space n) ℂ :=
  M.map n (maximalGroupCStarGenerator G g)

/-- The models are contractions: a unital completely positive map into matrices
is contractive (`Quasidiagonal.ucpContractive`), and the generators are
unitary, so of norm one. -/
theorem modelMatrix_norm_le_one (n : ℕ) (g : G) : ‖modelMatrix M n g‖ ≤ 1 := by
  have h := Quasidiagonal.ucpContractive.norm_le (MaximalGroupCStar G)
    inferInstance (M.space n) (M.map n) (M.map_one n) (M.completelyPositive n)
    (maximalGroupCStarGenerator G g)
  rwa [norm_maximalGroupCStarGenerator] at h

/-- The models preserve adjoints, so the adjoint of the model at `g` is the
model at `g⁻¹`. -/
theorem modelMatrix_conjTranspose (n : ℕ) (g : G) :
    (modelMatrix M n g)ᴴ = modelMatrix M n g⁻¹ := by
  rw [modelMatrix, modelMatrix, ← star_maximalGroupCStarGenerator G g,
    Quasidiagonal.ucp_map_star (M.map n) (M.map_one n) (M.completelyPositive n)]

/-- **The Gram defect vanishes.**  `x(g)⋆x(g) − 1` is the multiplicative defect
of the model at the pair `(u_{g⁻¹}, u_g)`, whose product is the unit. -/
theorem tendsto_hsNorm_gram (g : G) :
    Tendsto (fun n ↦ hsNorm (M.space n)
      ((modelMatrix M n g)ᴴ * modelMatrix M n g - 1)) atTop (nhds 0) := by
  have hone : maximalGroupCStarGenerator G g⁻¹ *
      maximalGroupCStarGenerator G g = 1 := by
    rw [maximalGroupCStarGenerator_mul, inv_mul_cancel,
      maximalGroupCStarGenerator_one]
  have hkey : ∀ n : ℕ, hsNorm (M.space n)
      ((modelMatrix M n g)ᴴ * modelMatrix M n g - 1)
      = hsNorm (M.space n)
        (M.map n (maximalGroupCStarGenerator G g⁻¹ *
            maximalGroupCStarGenerator G g)
          - M.map n (maximalGroupCStarGenerator G g⁻¹) *
              M.map n (maximalGroupCStarGenerator G g)) := by
    intro n
    rw [hsNorm_sub_comm, modelMatrix_conjTranspose, modelMatrix, modelMatrix,
      hone, M.map_one]
  simp only [hkey]
  exact M.tendsto_mul_hs (maximalGroupCStarGenerator G g⁻¹)
    (maximalGroupCStarGenerator G g)

/-- **The multiplicative defect vanishes**, at a pair of canonical
generators. -/
theorem tendsto_hsNorm_mul (g h : G) :
    Tendsto (fun n ↦ hsNorm (M.space n)
      (modelMatrix M n (g * h) - modelMatrix M n g * modelMatrix M n h))
      atTop (nhds 0) := by
  have hkey : ∀ n : ℕ,
      modelMatrix M n (g * h) - modelMatrix M n g * modelMatrix M n h
      = M.map n (maximalGroupCStarGenerator G g *
          maximalGroupCStarGenerator G h)
        - M.map n (maximalGroupCStarGenerator G g) *
            M.map n (maximalGroupCStarGenerator G h) := by
    intro n
    rw [modelMatrix, modelMatrix, modelMatrix, maximalGroupCStarGenerator_mul]
  simp only [hkey]
  exact M.tendsto_mul_hs (maximalGroupCStarGenerator G g)
    (maximalGroupCStarGenerator G h)

/-- The sequence that dominates the separation defect: the multiplicative
defect of the model at the pair `(u_g, u_{h⁻¹})` plus the error of the trace
clause at `u_{gh⁻¹}`.

It is a named function rather than an inline bound because `squeeze_zero`
assigns its dominating function to a metavariable: with an anonymous `fun n ↦
…` there, every later step of the pointwise estimate re-beta-reduces this whole
expression, and the elaboration exceeds the default heartbeat budget.  Naming
it makes the unification a constant application.  `scripts/check.py` forbids a
heartbeat-budget bump at any value --- its `maxHeartbeats` detector reads the
raw source, comments included --- so splitting the declaration is the legal
fix. -/
def separationBound (g h : G) (n : ℕ) : ℝ :=
  hsNorm (M.space n)
      (M.map n (maximalGroupCStarGenerator G g *
          maximalGroupCStarGenerator G h⁻¹)
        - M.map n (maximalGroupCStarGenerator G g) *
            M.map n (maximalGroupCStarGenerator G h⁻¹))
    + ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G (g * h⁻¹))
        - normTrace (M.space n)
            (M.map n (maximalGroupCStarGenerator G (g * h⁻¹)))‖

/-- The dominating sequence is null: both summands are, by
`AmenableTraceModel.tendsto_mul_hs` and `AmenableTraceModel.tendsto_trace`. -/
theorem tendsto_separationBound (g h : G) :
    Tendsto (separationBound M g h) atTop (nhds 0) := by
  have h1 := M.tendsto_mul_hs (maximalGroupCStarGenerator G g)
    (maximalGroupCStarGenerator G h⁻¹)
  have h2 := M.tendsto_trace (maximalGroupCStarGenerator G (g * h⁻¹))
  have h12 := h1.add h2
  rw [add_zero] at h12
  exact h12

/-- The pointwise half of the separation estimate: at every stage the trace of
`x(g)x(h)⋆` is dominated by `separationBound`.

The product is `φₙ(u_g)φₙ(u_{h⁻¹})` because the models preserve adjoints, and
`u_g u_{h⁻¹} = u_{gh⁻¹}`; the trace clause is applied at that generator, where
the hypothesis `hτ` says the canonical trace vanishes. -/
theorem norm_normTrace_le_separationBound (g h : G)
    (hτ : canonicalMaximalTrace G
      (maximalGroupCStarGenerator G (g * h⁻¹)) = 0) (n : ℕ) :
    ‖normTrace (M.space n)
        (modelMatrix M n g * (modelMatrix M n h)ᴴ)‖
      ≤ separationBound M g h n := by
  have hAB : maximalGroupCStarGenerator G g *
      maximalGroupCStarGenerator G h⁻¹
      = maximalGroupCStarGenerator G (g * h⁻¹) :=
    maximalGroupCStarGenerator_mul G g h⁻¹
  have hmodel : modelMatrix M n g * (modelMatrix M n h)ᴴ
      = M.map n (maximalGroupCStarGenerator G g) *
          M.map n (maximalGroupCStarGenerator G h⁻¹) := by
    rw [modelMatrix_conjTranspose, modelMatrix, modelMatrix]
  have hsplit : normTrace (M.space n)
      (M.map n (maximalGroupCStarGenerator G g) *
        M.map n (maximalGroupCStarGenerator G h⁻¹))
      = normTrace (M.space n)
          (M.map n (maximalGroupCStarGenerator G g) *
            M.map n (maximalGroupCStarGenerator G h⁻¹)
          - M.map n (maximalGroupCStarGenerator G (g * h⁻¹)))
        + normTrace (M.space n)
          (M.map n (maximalGroupCStarGenerator G (g * h⁻¹))) := by
    rw [normTrace_sub]
    ring
  rw [hmodel, hsplit, separationBound]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_normTrace_le_hsNorm _ _) (le_of_eq ?_)
    rw [hsNorm_sub_comm, hAB]
  · refine le_of_eq ?_
    rw [hτ, zero_sub, norm_neg]

/-- **The separation defect vanishes.**  For `g ≠ h` the product `x(g)x(h)⋆` is
asymptotically `x(gh⁻¹)`, whose normalized trace converges to `τ(u_{gh⁻¹})`,
and the canonical trace kills every nonidentity generator.

This is the only step that uses the canonical trace rather than an arbitrary
amenable one, and it is where the sharp separation constant comes from. -/
theorem tendsto_norm_normTrace_mul_conjTranspose (g h : G) (hgh : g ≠ h) :
    Tendsto (fun n ↦ ‖normTrace (M.space n)
      (modelMatrix M n g * (modelMatrix M n h)ᴴ)‖) atTop (nhds 0) := by
  have hne : g * h⁻¹ ≠ 1 := fun hcon ↦ hgh (mul_inv_eq_one.mp hcon)
  exact squeeze_zero (fun n ↦ norm_nonneg _)
    (norm_normTrace_le_separationBound M g h
      (canonicalMaximalTrace_generator_of_ne_one G hne))
    (tendsto_separationBound M g h)

/-- **The models are eventually nonempty.**  An empty model has normalized
trace `0` everywhere, while the trace clause at the unit forces that quantity
within any tolerance of `τ(1) = 1`. -/
theorem eventually_card_pos :
    ∀ᶠ n in atTop, 0 < Fintype.card (M.space n) := by
  have hone : canonicalMaximalTrace G 1 = 1 := canonicalMaximalTrace_one G
  have hlt : ∀ᶠ n in atTop,
      ‖canonicalMaximalTrace G 1
        - normTrace (M.space n) (M.map n 1)‖ < 1 :=
    (M.tendsto_trace 1).eventually_lt_const one_pos
  filter_upwards [hlt] with n hn
  by_contra hcard
  have hzero : Fintype.card (M.space n) = 0 := by omega
  have hnt : normTrace (M.space n) (M.map n 1) = 0 := by
    show Matrix.trace (M.map n 1)
      / ((Fintype.card (M.space n) : ℕ) : ℂ) = 0
    rw [hzero, Nat.cast_zero, div_zero]
  rw [hnt, hone, sub_zero, norm_one] at hn
  exact lt_irrefl 1 hn

end Model

/-! ## The theorem -/

/-- **An amenable canonical trace makes the group hyperlinear.**

Brown, Mem. Amer. Math. Soc. **184** (2006), no. 865, Theorem 3.1.7 `(1) ⟹ (2)`,
at the canonical trace of the full group C⋆-algebra.  By Brown's Theorem 4.1.9
the hypothesis is Kirchberg's factorization property for `G`.

The proof is the one the module docstring describes: choose one index at which
the Gram, multiplicative and separation defects are all below
`δ = min 1 (ε/22)` on the finite test set, polar-correct each model matrix to a
unitary, and pay the triangle inequalities.

No countability hypothesis appears. -/
theorem isHyperlinear_of_isAmenableTrace_canonicalMaximal (G : Type u)
    [Group G] (h : Quasidiagonal.IsAmenableTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) :
    IsHyperlinear G := by
  classical
  obtain ⟨M⟩ := h
  intro F ε hε
  obtain ⟨δ, hδpos, hδle, hδone⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε / 22 ∧ δ ≤ 1 :=
    ⟨min 1 (ε / 22), lt_min one_pos (by positivity), min_le_right _ _,
      min_le_left _ _⟩
  have hδmul : 22 * δ ^ 2 ≤ ε := by nlinarith
  have hδsep : 3 * δ ≤ ε / 2 := by linarith
  have hev : ∀ᶠ n in atTop, ∀ g ∈ F, ∀ h' ∈ F,
      hsNorm (M.space n)
          ((modelMatrix M n g)ᴴ * modelMatrix M n g - 1) ≤ δ ∧
        hsNorm (M.space n)
          ((modelMatrix M n h')ᴴ * modelMatrix M n h' - 1) ≤ δ ∧
        hsNorm (M.space n)
          ((modelMatrix M n (g * h'))ᴴ * modelMatrix M n (g * h') - 1) ≤ δ ∧
        hsNorm (M.space n) (modelMatrix M n (g * h')
          - modelMatrix M n g * modelMatrix M n h') ≤ δ ∧
        (‖normTrace (M.space n)
          (modelMatrix M n g * (modelMatrix M n h')ᴴ)‖ ≤ δ ∨ g = h') := by
    refine (Filter.eventually_all_finset F).mpr fun g _ ↦ ?_
    refine (Filter.eventually_all_finset F).mpr fun h' _ ↦ ?_
    by_cases hgh : g = h'
    · subst hgh
      filter_upwards [ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_hsNorm_gram M g) hδpos,
        ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_hsNorm_gram M (g * g)) hδpos,
        ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_hsNorm_mul M g g) hδpos] with n h1 h2 h3
      exact ⟨h1, h1, h2, h3, Or.inr rfl⟩
    · filter_upwards [ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_hsNorm_gram M g) hδpos,
        ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_hsNorm_gram M h') hδpos,
        ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_hsNorm_gram M (g * h')) hδpos,
        ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_hsNorm_mul M g h') hδpos,
        ShulmanTrace.eventually_le_of_tendsto_zero
          (tendsto_norm_normTrace_mul_conjTranspose M g h' hgh) hδpos] with
        n h1 h2 h3 h4 h5
      exact ⟨h1, h2, h3, h4, Or.inl h5⟩
  obtain ⟨n, hn, hcard⟩ := (hev.and (eventually_card_pos M)).exists
  haveI : Nonempty (M.space n) := Fintype.card_pos_iff.mp hcard
  choose w hw hwle using fun g : G ↦
    HilbertSchmidtPolar.exists_unitary_hsNorm_sub_le (M.space n)
      (modelMatrix M n g)
  refine ⟨{
    carrier := M.space n
    nonempty := hcard
    map := w
    isUnitary := hw
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h' hh'
    obtain ⟨hg1, hh1, hgh1, hmul, -⟩ := hn g hg h' hh'
    have hA : hsNormSq (M.space n)
        (w (g * h') - modelMatrix M n (g * h')) ≤ δ ^ 2 :=
      hsNormSq_le_sq_of_hsNorm_le _ ((hwle (g * h')).trans hgh1)
    have hB : hsNormSq (M.space n) (modelMatrix M n (g * h')
        - modelMatrix M n g * modelMatrix M n h') ≤ δ ^ 2 :=
      hsNormSq_le_sq_of_hsNorm_le _ hmul
    have hC : hsNormSq (M.space n)
        (modelMatrix M n g * modelMatrix M n h' - w g * w h')
        ≤ 4 * δ ^ 2 :=
      hsNormSq_mul_sub_mul_le _ (modelMatrix_norm_le_one M n h')
        (le_of_eq (CStarRing.norm_of_mem_unitary (hw g)))
        ((hwle g).trans hg1) ((hwle h').trans hh1)
    have hsplit : w (g * h') - w g * w h'
        = (w (g * h') - modelMatrix M n (g * h'))
          + ((modelMatrix M n (g * h')
              - modelMatrix M n g * modelMatrix M n h')
            + (modelMatrix M n g * modelMatrix M n h' - w g * w h')) := by
      abel
    have hadd1 := hsNormSq_add_le (M.space n)
      (modelMatrix M n (g * h') - modelMatrix M n g * modelMatrix M n h')
      (modelMatrix M n g * modelMatrix M n h' - w g * w h')
    have hadd2 := hsNormSq_add_le (M.space n)
      (w (g * h') - modelMatrix M n (g * h'))
      ((modelMatrix M n (g * h')
          - modelMatrix M n g * modelMatrix M n h')
        + (modelMatrix M n g * modelMatrix M n h' - w g * w h'))
    rw [hsDistSq_eq_hsNormSq_sub, hsplit]
    linarith
  · intro g hg h' hh' hne
    obtain ⟨hg1, hh1, -, -, hsep⟩ := hn g hg h' hh'
    rcases hsep with hsep | hcon
    · rw [hsDistSq_of_unitary (M.space n) (hw g) (hw h') hcard]
      have hunit : ‖w g‖ = 1 := CStarRing.norm_of_mem_unitary (hw g)
      have hstar : ‖(modelMatrix M n h')ᴴ‖ ≤ 1 := by
        rw [← Matrix.star_eq_conjTranspose, norm_star]
        exact modelMatrix_norm_le_one M n h'
      have hconj : hsNorm (M.space n)
          ((w h')ᴴ - (modelMatrix M n h')ᴴ) ≤ δ := by
        rw [← Matrix.conjTranspose_sub, hsNorm_conjTranspose]
        exact (hwle h').trans hh1
      have hprod : hsNormSq (M.space n)
          (modelMatrix M n g * (modelMatrix M n h')ᴴ - w g * (w h')ᴴ)
          ≤ 4 * δ ^ 2 :=
        hsNormSq_mul_sub_mul_le _ hstar (le_of_eq hunit)
          ((hwle g).trans hg1) hconj
      have hprodnorm : hsNorm (M.space n)
          (modelMatrix M n g * (modelMatrix M n h')ᴴ - w g * (w h')ᴴ)
          ≤ 2 * δ := by
        refine hsNorm_le_of_hsNormSq_le _ (by positivity) ?_
        calc hsNormSq (M.space n)
              (modelMatrix M n g * (modelMatrix M n h')ᴴ - w g * (w h')ᴴ)
            ≤ 4 * δ ^ 2 := hprod
          _ = (2 * δ) ^ 2 := by ring
      have hdiff : normTrace (M.space n) (w g * (w h')ᴴ)
          = normTrace (M.space n)
              (w g * (w h')ᴴ
                - modelMatrix M n g * (modelMatrix M n h')ᴴ)
            + normTrace (M.space n)
              (modelMatrix M n g * (modelMatrix M n h')ᴴ) := by
        rw [normTrace_sub]
        ring
      have hbound : ‖normTrace (M.space n)
          (w g * (w h')ᴴ - modelMatrix M n g * (modelMatrix M n h')ᴴ)‖
          ≤ 2 * δ := by
        refine le_trans (norm_normTrace_le_hsNorm _ _) ?_
        rw [hsNorm_sub_comm]
        exact hprodnorm
      have htr : ‖normTrace (M.space n) (w g * (w h')ᴴ)‖ ≤ 3 * δ := by
        rw [hdiff]
        refine le_trans (norm_add_le _ _) ?_
        linarith
      have hre : (normTrace (M.space n) (w g * (w h')ᴴ)).re ≤ 3 * δ :=
        le_trans (Complex.re_le_norm _) htr
      linarith
    · exact absurd hcon hne

end

end AmenableTraceHyperlinear

end GroupApproximation
