import GroupApproximation.Analysis.LIXPowersNaturality

/-!
# Eckmann--Hilton for clutching functions

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3 item 1.  The `k`-th *pointwise* power `u^k`
of a clutching function has to be replaced, up to homotopy, by a single *composite*
`u ∘ ψ_k`, so that the naturality of clutching (`Analysis/LIXPowersNaturality.lean`) can
turn it into a pullback and Step C can count zeros.  That replacement is the
Eckmann--Hilton argument, and this file is its formula-level form.

## The lemma, and why it needs no basepoint

The classical Eckmann--Hilton statement -- "on a suspension, the pointwise product and the
pinch sum of two group-valued maps agree" -- is usually stated for *based* maps, and the
basepoints are what make the pinch sum defined at all.  The half of it that the powers
argument actually consumes is unconditional, and it is this:

> **Interchange.**  Let `P j` be a continuous family of self-maps of the closed unit ball
> of `E`, one for each factor `j < k`, starting at the identity at time `0`.  Then the
> pointwise power `u^k` is homotopic, through unitary-valued maps, to the ordered product
> `∏_{j<k} (u ∘ P j 1)` of the reparametrised copies.

There is no hypothesis on `u` whatsoever: the homotopy is
`H θ y = (u y)^k`-adjoint times `∏_{j<k} u (P j θ y)`, which at `θ = 0` is the identity
because every `P j 0` is the identity, and the whole content of the construction sits in
the *choice* of the family `P`, not in the homotopy.

Basepoints re-enter exactly once, and only to *rename* the answer: to collapse the ordered
product `∏_{j<k} (u ∘ P j 1)` into a single composite `u ∘ ψ_k`, the factors have to be
supported in disjoint regions and `u` has to be `1` off the support of each.  That is
`PinchIdentification` below -- a named `Prop`, discharged by `sp-design` together with the
choice of `ψ_k`, never by this file.

The family `P` for which the identification is intended is the **angle family** of the join
power `ψ_k` of `Analysis/LIXPowersJoinPower.lean`, agreed with `sp-design` (their §2.4(c)):
`A_{j,θ}(z, v) = (|z| e^{i c_{j,θ}(arg z)}, v)` with
`c_{j,θ}(φ) = clamp ((1 + θ(k−1))(φ+π) − 2πθj, 0, 2π) − π`.  Its two ends are the *same*
set -- the wall `{z ∈ ℝ_{≥0}}` -- so the pinch interfaces match automatically, each
`A_{j,θ}` is a continuous self-map of `E` (no gluing of matrix products anywhere), and the
basepoint condition is `u ≡ 1` on the wall rather than at a pole.

The alternative considered and dropped was a `k`-slab family in a suspension coordinate.
Its time-1 maps are honest continuous self-maps of the sphere ("collapse below the slab to
the south pole, above it to the north pole, stretch the slab over the sphere"), but they
assemble into a *discontinuous* vertical pinch -- slab `j`'s top goes to the north pole and
slab `j+1`'s bottom to the south pole -- so it can discharge `PinchIdentification` only for
a `ψ_k` that is not a map, which is useless to
`Analysis/LIXPowersNaturality.lean`.

## Main results

* `reparProd` -- the ordered product of the first `k` reparametrised copies, by recursion
  on `k`, so that continuity and unitarity are two-line inductions.
* `exists_partialIsometry_pow_reparProd` -- **the Eckmann--Hilton step**: `clutch (u^k)`
  and `clutch (∏_{j<k} u ∘ P j 1)` are Murray--von Neumann equivalent as continuous
  fields.
* `exists_partialIsometry_pow_pullback` -- **items 1--3 of §1.3 in one statement**: with
  the pinch identification and a radial `Ψ`, `clutch (u^k)` is equivalent to the pullback
  of `clutch u` along the suspension of `ψ`.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

section Repar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]
  {W : E → Matrix n n ℂ} {P : ℕ → ℝ → E → E}

/-- **The ordered product of the first `k` reparametrised copies** of a clutching
function.  Recursion on `k` rather than a `Finset` product, because the matrix ring is not
commutative and because it makes every property below a two-line induction. -/
def reparProd (W : E → Matrix n n ℂ) (P : ℕ → ℝ → E → E) (θ : ℝ) (y : E) :
    ℕ → Matrix n n ℂ
  | 0 => 1
  | j + 1 => reparProd W P θ y j * W (P j θ y)

theorem reparProd_zero (W : E → Matrix n n ℂ) (P : ℕ → ℝ → E → E) (θ : ℝ) (y : E) :
    reparProd W P θ y 0 = 1 := rfl

theorem reparProd_succ (W : E → Matrix n n ℂ) (P : ℕ → ℝ → E → E) (θ : ℝ) (y : E)
    (j : ℕ) : reparProd W P θ y (j + 1) = reparProd W P θ y j * W (P j θ y) := rfl

/-- At time `0` every reparametrisation is the identity, so the ordered product is the
pointwise power. -/
theorem reparProd_param_zero (hP0 : ∀ (j : ℕ) (y : E), P j 0 y = y) (W : E → Matrix n n ℂ)
    (y : E) (k : ℕ) : reparProd W P 0 y k = (W y) ^ k := by
  induction k with
  | zero => rw [reparProd_zero, pow_zero]
  | succ j ih => rw [reparProd_succ, ih, hP0 j y, pow_succ]

theorem continuous_reparProd (hW : Continuous W)
    (hPc : ∀ j : ℕ, Continuous fun p : ℝ × E => P j p.1 p.2) (k : ℕ) :
    Continuous fun p : ℝ × E => reparProd W P p.1 p.2 k := by
  induction k with
  | zero =>
      simp only [reparProd_zero]
      exact continuous_const
  | succ j ih =>
      simp only [reparProd_succ]
      exact ih.matrix_mul (hW.comp (hPc j))

theorem unit_reparProd (hW : IsBallUnitary W)
    (hPb : ∀ (j : ℕ) (θ : ℝ) (y : E), ‖y‖ ≤ 1 → ‖P j θ y‖ ≤ 1) (θ : ℝ) {y : E}
    (hy : ‖y‖ ≤ 1) (k : ℕ) :
    (reparProd W P θ y k)ᴴ * reparProd W P θ y k = 1 ∧
      reparProd W P θ y k * (reparProd W P θ y k)ᴴ = 1 := by
  induction k with
  | zero =>
      rw [reparProd_zero]
      simp
  | succ j ih =>
      rw [reparProd_succ]
      exact unit_mul ih ⟨hW.star_mul_self _ (hPb j θ y hy), hW.mul_star_self _ (hPb j θ y hy)⟩

/-- A pointwise power of a ball unitary is a ball unitary. -/
theorem IsBallUnitary.pow (hW : IsBallUnitary W) (k : ℕ) :
    IsBallUnitary fun y => (W y) ^ k := by
  induction k with
  | zero =>
      constructor
      · simp only [pow_zero]
        exact continuous_const
      · intro y _
        simp
      · intro y _
        simp
  | succ j ih =>
      have h := ih.mul hW
      simpa only [pow_succ] using h

end Repar

/-! ## The Eckmann--Hilton step -/

section Step

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n]
  {t : X → ℝ} {ν : X → E} {W : E → Matrix n n ℂ} {P : ℕ → ℝ → E → E} {Ψ : E → E}

/-- **Eckmann--Hilton for clutching functions.**  The projection clutched by the `k`-th
pointwise power of `W` is Murray--von Neumann equivalent, through an explicit continuous
partial isometry, to the projection clutched by the ordered product of the `k`
reparametrised copies of `W`.  No hypothesis on `W` beyond unitarity on the ball, and
none at all on the reparametrisation family beyond continuity, `P j 0 = id`, and
preservation of the ball. -/
theorem exists_partialIsometry_pow_reparProd (hc : IsSuspensionChart t ν)
    (hW : IsBallUnitary W)
    (hPc : ∀ j : ℕ, Continuous fun p : ℝ × E => P j p.1 p.2)
    (hP0 : ∀ (j : ℕ) (y : E), P j 0 y = y)
    (hPb : ∀ (j : ℕ) (θ : ℝ) (y : E), ‖y‖ ≤ 1 → ‖P j θ y‖ ≤ 1) (k : ℕ) :
    ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x =
        clutchMat (t x) (coneMat (fun y => reparProd W P 1 y k) (ν x))) ∧
      (∀ x, V x * (V x)ᴴ = clutchMat (t x) (coneMat (fun y => (W y) ^ k) (ν x))) := by
  have hpow := hW.pow k
  refine exists_partialIsometry_of_homotopy hc hpow
    (H := fun θ y => ((W y) ^ k)ᴴ * reparProd W P θ y k) ?_ ?_ ?_ ?_ ?_
  · have h1 : Continuous fun p : ℝ × E => ((W p.2) ^ k)ᴴ :=
      (hpow.continuous.comp continuous_snd).matrix_conjTranspose
    exact h1.matrix_mul (continuous_reparProd hW.continuous hPc k)
  · intro y hy
    rw [reparProd_param_zero hP0]
    exact hpow.star_mul_self y hy
  · intro θ y _ _ hy
    exact (unit_mul (unit_star ⟨hpow.star_mul_self y hy, hpow.mul_star_self y hy⟩)
      (unit_reparProd hW hPb θ hy k)).1
  · intro θ y _ _ hy
    exact (unit_mul (unit_star ⟨hpow.star_mul_self y hy, hpow.mul_star_self y hy⟩)
      (unit_reparProd hW hPb θ hy k)).2
  · intro y hy
    rw [← Matrix.mul_assoc, hpow.mul_star_self y (le_of_eq hy), Matrix.one_mul]

/-- **The pinch identification**, the single hypothesis this lane does not discharge.

The Eckmann--Hilton step lands on the *ordered product* of the `k` reparametrised copies;
Step C needs a single *composite* `W ∘ ψ_k`.  Collapsing the product to the composite is
where the basepoint conditions live, and it is a property of the pair
(reparametrisation family, `ψ_k`) together with the normalisation of `W`.  `sp-design`
owns `ψ_k` and discharges this; nothing here proves an instance of it.

For the `k`-slab family in a suspension coordinate the identification holds exactly when
`W` takes the value `1` at both poles, and for the join power
`ψ_k (z, v) = (z^k/|z|^{k-1}, v)` exactly when `W` is `1` on the cut half-disc; see
`notes/lix-stronger-lane-reports/sp-powers.md` §0 and §2. -/
def PinchIdentification (W : E → Matrix n n ℂ) (P : ℕ → ℝ → E → E) (Ψ : E → E) (k : ℕ) :
    Prop :=
  ∀ y : E, ‖y‖ = 1 → reparProd W P 1 y k = W (Ψ y)

/-- **Items 1--3 of §1.3, in one statement.**  Given the pinch identification and a radial
`ψ_k`, the projection clutched by `W^k` is Murray--von Neumann equivalent, through an
explicit continuous partial isometry, to the projection clutched by `W` over the
*suspended* chart `(t, Ψ ∘ ν)` -- i.e. to the pullback of `clutch W` along `Σψ_k`. -/
theorem exists_partialIsometry_pow_pullback (hc : IsSuspensionChart t ν)
    (hW : IsBallUnitary W)
    (hPc : ∀ j : ℕ, Continuous fun p : ℝ × E => P j p.1 p.2)
    (hP0 : ∀ (j : ℕ) (y : E), P j 0 y = y)
    (hPb : ∀ (j : ℕ) (θ : ℝ) (y : E), ‖y‖ ≤ 1 → ‖P j θ y‖ ≤ 1)
    (hΨ : IsRadialMap Ψ) {k : ℕ} (hpinch : PinchIdentification W P Ψ k) :
    ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x = clutchMat (t x) (coneMat W (Ψ (ν x)))) ∧
      (∀ x, V x * (V x)ᴴ = clutchMat (t x) (coneMat (fun y => (W y) ^ k) (ν x))) := by
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_pow_reparProd hc hW hPc hP0 hPb k
  refine ⟨V, hVc, fun x => ?_, hV2⟩
  rw [hV1 x, coneMat_comp_radial hΨ]
  congr 1
  exact coneMat_congr (fun y hy => hpinch y hy) (ν x)

/-- The Eckmann--Hilton step transported along a realisation of `Σψ_k` as an honest
self-map `Φ` of the parameter space: the clutched projection of `W^k` is equivalent to the
clutched projection of `W` read at `Φ x`. -/
theorem exists_partialIsometry_pow_pullback_map (hc : IsSuspensionChart t ν)
    (hW : IsBallUnitary W)
    (hPc : ∀ j : ℕ, Continuous fun p : ℝ × E => P j p.1 p.2)
    (hP0 : ∀ (j : ℕ) (y : E), P j 0 y = y)
    (hPb : ∀ (j : ℕ) (θ : ℝ) (y : E), ‖y‖ ≤ 1 → ‖P j θ y‖ ≤ 1)
    (hΨ : IsRadialMap Ψ) {k : ℕ} (hpinch : PinchIdentification W P Ψ k)
    {Φ : X → X} (hΦt : ∀ x, t (Φ x) = t x) (hΦν : ∀ x, ν (Φ x) = Ψ (ν x)) :
    ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x = clutchMat (t (Φ x)) (coneMat W (ν (Φ x)))) ∧
      (∀ x, V x * (V x)ᴴ = clutchMat (t x) (coneMat (fun y => (W y) ^ k) (ν x))) := by
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_pow_pullback hc hW hPc hP0 hPb hΨ hpinch
  refine ⟨V, hVc, fun x => ?_, hV2⟩
  rw [hV1 x, hΦt, hΦν]

end Step

end

end Powers
end LIX
end GroupApproximation
