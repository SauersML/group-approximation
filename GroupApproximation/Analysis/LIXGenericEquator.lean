import GroupApproximation.Analysis.LIXGeneratorUnitary

set_option autoImplicit false

/-!
# The equator of `S^{2n+1}` as a copy of `S^{2n}`, and the generator on it

`Analysis/LIXGeneratorUnitary.lean` builds the seam generator `Gen.genU n` as a unitary of
`ℂ^{n+1}` fixing the pole `Gen.ePole n`, over the equator `{x : Re (x (Fin.last n)) = 0}` of
the *complex* sphere `S^{2n+1} ⊂ ℂ^{n+1}`.  This file carries it to the *real* equatorial
space `E n = EuclideanSpace ℝ (Fin (2n+1))`, whose unit sphere is `S^{2n}`, which is the
vocabulary the tower (`STW59.Gen.sphereEven`) and lane `sp-powers` both work in.

At `n = 2` all of this exists already, unprimed, in `Analysis/LIXLemmaSixGenerator.lean`
(`equatorEmb`, `incl`, `genU2`, `genMat`).  This file is the general-rank version; the
`n = 2` specialisation is deliberately **not** wired up here, because the existing one is
green and is what the endpoint chain is stated against.

## The embedding, and why its shape is the whole point

`Gen.equatorEmb n` pairs the first `2n` real coordinates into `n` complex ones and sends
the last real coordinate to a purely imaginary number:

```text
a ↦ (a₀ + i a₁, a₂ + i a₃, …, a_{2n-2} + i a_{2n-1}, i a_{2n})
```

Two facts about it hold for **every** `a`, with no norm hypothesis, and they are what make
the generator usable as a function on the equatorial space:

* `Gen.re_equatorEmb_last` — the last complex coordinate is purely imaginary.  So the image
  always lies on the equator, `x (Fin.last n)` is never `±1`, and *both* hemisphere frames
  are defined at every point.  This is the only reason a total formula is available at all.
* `Gen.sum_norm_sq_equatorEmb` — `∑ᵢ ‖(equatorEmb n a) i‖² = ‖a‖²`, so the embedding is an
  isometry, and a unit vector of `E n` goes to a unit vector of `ℂ^{n+1}`.

The norm hypothesis is therefore the *only* one that fails off the sphere, and radial
normalisation repairs it: `Gen.genSphere n` below is continuous and unitary at every
`y ≠ 0`.

## What cannot be had, and why

There is no extension of the generator to a **ball** unitary.  The Householder chain
underneath it normalises for unit vectors twice over:
`midNorm p x = √(2 + 2 Re ⟨p,x⟩)` is the length of `p + x` *only* when `p` and `x` are unit
vectors, and it vanishes on the whole half-space `Re ⟨p,x⟩ ≤ -1`, where Lean's `x / 0 = 0`
collapses `midVec` to the zero vector; and `transPhase a b = ⟨a,b⟩ / ‖⟨a,b⟩‖` is
discontinuous wherever `⟨a,b⟩ = 0`, which off the sphere is a set of codimension one rather
than the excluded antipode.  Unitarity of `seamGen` is derived from `IsFrameDatum`, whose
`unit_x` field is load-bearing.  So the honest interface for `sp-powers` is *sphere*, or a
shell, never the closed ball.

## Status

**Authored, not yet probed.**  Nothing imports this file, deliberately: the `n = 2`
closure is a verified artifact and this module must not be able to redden it before it has
been through a gate of its own.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

open scoped Matrix

noncomputable section

/-! ### `ℝ^{2n+1}` indexed as `n` real pairs plus one -/

/-- The coordinate of `ℝ^{2n+1}` carrying the `b`-th real part of the `i`-th complex
coordinate (`b = 0` real, `b = 1` imaginary), and `2n` for the equator coordinate. -/
def eqFwd (n : ℕ) : (Fin n × Fin 2) ⊕ Unit → Fin (2 * n + 1)
  | Sum.inl (i, b) => ⟨2 * (i : ℕ) + (b : ℕ), by
      have hi := i.isLt
      have hb := b.isLt
      omega⟩
  | Sum.inr _ => ⟨2 * n, by omega⟩

/-- The inverse of `eqFwd`: divide by two. -/
def eqBwd (n : ℕ) (k : Fin (2 * n + 1)) : (Fin n × Fin 2) ⊕ Unit :=
  if h : (k : ℕ) < 2 * n then
    Sum.inl (⟨(k : ℕ) / 2, by omega⟩, ⟨(k : ℕ) % 2, by omega⟩)
  else Sum.inr ()

@[simp] theorem eqFwd_inl_val (n : ℕ) (i : Fin n) (b : Fin 2) :
    ((eqFwd n (Sum.inl (i, b)) : Fin (2 * n + 1)) : ℕ) = 2 * (i : ℕ) + (b : ℕ) := rfl

@[simp] theorem eqFwd_inr_val (n : ℕ) (u : Unit) :
    ((eqFwd n (Sum.inr u) : Fin (2 * n + 1)) : ℕ) = 2 * n := rfl

theorem eqBwd_eqFwd (n : ℕ) (s : (Fin n × Fin 2) ⊕ Unit) : eqBwd n (eqFwd n s) = s := by
  rcases s with ⟨i, b⟩ | ⟨⟩
  · have hi := i.isLt
    have hb := b.isLt
    simp only [eqBwd, eqFwd_inl_val]
    rw [dif_pos (show 2 * (i : ℕ) + (b : ℕ) < 2 * n by omega)]
    refine congrArg Sum.inl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
    · show (2 * (i : ℕ) + (b : ℕ)) / 2 = (i : ℕ)
      omega
    · show (2 * (i : ℕ) + (b : ℕ)) % 2 = (b : ℕ)
      omega
  · simp only [eqBwd, eqFwd_inr_val]
    rw [dif_neg (show ¬ (2 * n < 2 * n) by omega)]

theorem eqFwd_eqBwd (n : ℕ) (k : Fin (2 * n + 1)) : eqFwd n (eqBwd n k) = k := by
  have hk := k.isLt
  by_cases h : (k : ℕ) < 2 * n
  · rw [eqBwd, dif_pos h]
    refine Fin.ext ?_
    show 2 * ((k : ℕ) / 2) + (k : ℕ) % 2 = (k : ℕ)
    omega
  · rw [eqBwd, dif_neg h]
    refine Fin.ext ?_
    show 2 * n = (k : ℕ)
    omega

/-- `ℝ^{2n+1}` indexed as `n` real pairs plus one extra coordinate. -/
def eqIdx (n : ℕ) : ((Fin n × Fin 2) ⊕ Unit) ≃ Fin (2 * n + 1) where
  toFun := eqFwd n
  invFun := eqBwd n
  left_inv := eqBwd_eqFwd n
  right_inv := eqFwd_eqBwd n

@[simp] theorem eqIdx_apply (n : ℕ) (s : (Fin n × Fin 2) ⊕ Unit) : eqIdx n s = eqFwd n s := rfl

/-! ### The embedding -/

/-- **The equator embedding** `E n = ℝ^{2n+1} → ℂ^{n+1}`, landing in
`Re (x (Fin.last n)) = 0`.  The first `2n` real coordinates pair up into `n` complex ones
and the last becomes purely imaginary. -/
def equatorEmb (n : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) : Fin (n + 1) → ℂ :=
  Fin.snoc
    (fun i : Fin n =>
      ((a (eqFwd n (Sum.inl (i, 0))) : ℝ) : ℂ)
        + ((a (eqFwd n (Sum.inl (i, 1))) : ℝ) : ℂ) * Complex.I)
    (((a (eqFwd n (Sum.inr ())) : ℝ) : ℂ) * Complex.I)

@[simp]
theorem equatorEmb_castSucc (n : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) (i : Fin n) :
    equatorEmb n a i.castSucc
      = ((a (eqFwd n (Sum.inl (i, 0))) : ℝ) : ℂ)
        + ((a (eqFwd n (Sum.inl (i, 1))) : ℝ) : ℂ) * Complex.I := by
  rw [equatorEmb, Fin.snoc_castSucc]

@[simp]
theorem equatorEmb_last (n : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    equatorEmb n a (Fin.last n) = ((a (eqFwd n (Sum.inr ())) : ℝ) : ℂ) * Complex.I := by
  rw [equatorEmb, Fin.snoc_last]

/-- **The image lies on the equator**, for every `a`: the last coordinate is purely
imaginary.  No norm hypothesis, and this is what keeps both hemisphere frames defined. -/
theorem re_equatorEmb_last (n : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    (equatorEmb n a (Fin.last n)).re = 0 := by
  rw [equatorEmb_last]
  simp [Complex.mul_re]

/-! ### The embedding is an isometry -/

/-- The squared modulus of `x + y i` for real `x, y`. -/
private theorem normSq_ofReal_add_mul_I (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]

private theorem normSq_ofReal_mul_I (y : ℝ) :
    ‖(y : ℂ) * Complex.I‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]

/-- **`Gen.equatorEmb n` is an isometry**, for every `a`. -/
theorem sum_norm_sq_equatorEmb (n : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    ∑ i, ‖equatorEmb n a i‖ ^ 2 = ‖a‖ ^ 2 := by
  classical
  have hL : ∑ i, ‖equatorEmb n a i‖ ^ 2
      = (∑ i : Fin n, (‖a (eqFwd n (Sum.inl (i, 0)))‖ ^ 2
            + ‖a (eqFwd n (Sum.inl (i, 1)))‖ ^ 2))
        + ‖a (eqFwd n (Sum.inr ()))‖ ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) ?_
    · rw [equatorEmb_castSucc, normSq_ofReal_add_mul_I]
    · rw [equatorEmb_last, normSq_ofReal_mul_I]
  have hR : ‖a‖ ^ 2 = ∑ k : Fin (2 * n + 1), ‖a k‖ ^ 2 := EuclideanSpace.norm_sq_eq a
  have hE : ∑ k : Fin (2 * n + 1), ‖a k‖ ^ 2
      = ∑ s : (Fin n × Fin 2) ⊕ Unit, ‖a (eqFwd n s)‖ ^ 2 :=
    (Fintype.sum_equiv (eqIdx n) (fun s => ‖a (eqFwd n s)‖ ^ 2) (fun k => ‖a k‖ ^ 2)
      (fun s => by rw [eqIdx_apply])).symm
  have hS : ∑ s : (Fin n × Fin 2) ⊕ Unit, ‖a (eqFwd n s)‖ ^ 2
      = (∑ p : Fin n × Fin 2, ‖a (eqFwd n (Sum.inl p))‖ ^ 2)
        + ‖a (eqFwd n (Sum.inr ()))‖ ^ 2 := by
    rw [Fintype.sum_sum_type]
    refine congrArg₂ (· + ·) rfl ?_
    simp
  have hP : ∑ p : Fin n × Fin 2, ‖a (eqFwd n (Sum.inl p))‖ ^ 2
      = ∑ i : Fin n, (‖a (eqFwd n (Sum.inl (i, 0)))‖ ^ 2
          + ‖a (eqFwd n (Sum.inl (i, 1)))‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_two _
  rw [hL, hR, hE, hS, hP]

/-- A unit vector of `E n` goes to a unit vector of `ℂ^{n+1}`. -/
theorem equatorEmb_mem (n : ℕ) {a : EuclideanSpace ℝ (Fin (2 * n + 1))} (ha : ‖a‖ = 1) :
    equatorEmb n a ∈ STW59.unitVectors (Fin (n + 1)) := by
  show ∑ i, ‖equatorEmb n a i‖ ^ 2 = 1
  rw [sum_norm_sq_equatorEmb, ha, one_pow]

theorem continuous_equatorEmb (n : ℕ) : Continuous (equatorEmb n) := by
  have h : ∀ k : Fin (2 * n + 1),
      Continuous fun a : EuclideanSpace ℝ (Fin (2 * n + 1)) => ((a k : ℝ) : ℂ) :=
    fun k => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ => ℝ) k)
  refine continuous_pi fun j => ?_
  refine Fin.lastCases ?_ ?_ j
  · simp only [equatorEmb_last]
    exact (h (eqFwd n (Sum.inr ()))).mul continuous_const
  · intro i
    simp only [equatorEmb_castSucc]
    exact (h (eqFwd n (Sum.inl (i, 0)))).add
      ((h (eqFwd n (Sum.inl (i, 1)))).mul continuous_const)

/-- Both hemisphere frames are defined at every point of the image. -/
theorem equatorEmb_ne_neg_one (n : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    equatorEmb n a (Fin.last n) ≠ -1 :=
  ne_neg_one_of_re_eq_zero (re_equatorEmb_last n a)

theorem equatorEmb_ne_one (n : ℕ) (a : EuclideanSpace ℝ (Fin (2 * n + 1))) :
    equatorEmb n a (Fin.last n) ≠ 1 :=
  ne_one_of_re_eq_zero (re_equatorEmb_last n a)

theorem isEquator_equatorEmb (n : ℕ) {a : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (ha : ‖a‖ = 1) : IsEquator (ePole n) (equatorEmb n a) :=
  isEquator_ePole (equatorEmb_mem n ha) (re_equatorEmb_last n a)

/-! ### The `n × n` block of the generator -/

/-- The isometry of `ℂ^n` onto `pole^⊥ ⊆ ℂ^{n+1}`: the standard basis vector `j` of `ℂ^n`
goes to the standard basis vector `j.castSucc`, so the pole `Fin.last n` is missed. -/
def incl (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  Matrix.of fun i j => if i = j.castSucc then 1 else 0

theorem incl_apply (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    incl n i j = if i = j.castSucc then 1 else 0 := rfl

theorem incl_conjTranspose_mul (n : ℕ) : (incl n)ᴴ * incl n = 1 := by
  classical
  refine Matrix.ext fun j j' => ?_
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (j.castSucc)]
  · rw [Matrix.conjTranspose_apply, incl_apply, incl_apply, if_pos rfl]
    by_cases h : j = j'
    · subst h; simp
    · have hc : ¬ (j.castSucc = j'.castSucc) := fun hcc => h (Fin.castSucc_injective n hcc)
      simp [hc, h]
  · intro i _ hi
    rw [Matrix.conjTranspose_apply, incl_apply, if_neg hi, star_zero, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ (j.castSucc)) hcon

theorem ePole_apply (n : ℕ) (i : Fin (n + 1)) :
    ePole n i = if i = Fin.last n then (1 : ℂ) else 0 := by
  classical
  rw [ePole]
  by_cases h : i = Fin.last n
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg h]

/-- **`incl` cuts out the pole**: its range projection is the complement of the pole line. -/
theorem incl_mul_conjTranspose (n : ℕ) :
    incl n * (incl n)ᴴ = 1 - rk1 (ePole n) (ePole n) := by
  classical
  refine Matrix.ext fun i i' => ?_
  rw [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, rk1_apply, ePole_apply,
    ePole_apply]
  refine Fin.lastCases ?_ ?_ i
  · have hzero : ∀ j : Fin n, incl n (Fin.last n) j * (incl n)ᴴ j i' = 0 := by
      intro j
      rw [incl_apply, if_neg (Fin.castSucc_lt_last j).ne', zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hzero j, Finset.sum_const_zero, if_pos rfl, one_mul]
    by_cases h : (Fin.last n : Fin (n + 1)) = i'
    · subst h
      simp
    · have h' : ¬ (i' = Fin.last n) := fun hc => h hc.symm
      rw [if_neg h, if_neg h']
      simp
  · intro k
    have hne : (k.castSucc : Fin (n + 1)) ≠ Fin.last n := (Fin.castSucc_lt_last k).ne
    rw [if_neg hne, zero_mul, sub_zero]
    have hterm : ∀ j : Fin n, incl n k.castSucc j * (incl n)ᴴ j i'
        = if j = k then (incl n)ᴴ k i' else 0 := by
      intro j
      rw [incl_apply]
      by_cases h : (k.castSucc : Fin (n + 1)) = j.castSucc
      · have hjk : j = k := (Fin.castSucc_injective n h).symm
        subst hjk
        simp
      · have hjk : j ≠ k := fun hc => by subst hc; exact h rfl
        simp [h, hjk]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_eq_single k]
    · rw [if_pos rfl, Matrix.conjTranspose_apply, incl_apply]
      by_cases h : i' = (k.castSucc : Fin (n + 1))
      · subst h
        simp
      · have hsw : ¬ ((k.castSucc : Fin (n + 1)) = i') := fun hc => h hc.symm
        rw [if_neg h, if_neg hsw, star_zero]
    · intro j _ hj
      rw [if_neg hj]
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon

/-- Compressing a unitary that commutes with `s sᴴ` by the isometry `s` gives a unitary.
The rank-generic form of `LIXLemmaSixGenerator.conjTranspose_mul_self_of_comm`: no rank
argument and no determinant, only `sᴴ s = 1`. -/
theorem conjTranspose_mul_self_of_comm {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] {s : Matrix m k ℂ} (hs : sᴴ * s = 1) {A : Matrix m m ℂ} (hA : Aᴴ * A = 1)
    (hcomm : A * (s * sᴴ) = (s * sᴴ) * A) :
    (sᴴ * A * s)ᴴ * (sᴴ * A * s) = 1 := by
  have h1 : (sᴴ * A * s)ᴴ = sᴴ * Aᴴ * s := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [h1]
  calc sᴴ * Aᴴ * s * (sᴴ * A * s)
      = sᴴ * (Aᴴ * (s * sᴴ * A)) * s := by simp only [Matrix.mul_assoc]
    _ = sᴴ * (Aᴴ * (A * (s * sᴴ))) * s := by rw [hcomm]
    _ = sᴴ * (Aᴴ * A * (s * sᴴ)) * s := by simp only [Matrix.mul_assoc]
    _ = sᴴ * (s * sᴴ) * s := by rw [hA, Matrix.one_mul]
    _ = 1 := by
        simp only [Matrix.mul_assoc]
        rw [hs, Matrix.mul_one, hs]

/-- **The `n × n` block of the seam generator**: the manuscript's `u`, at rank `n`. -/
def genU2 (n : ℕ) (x : Fin (n + 1) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (incl n)ᴴ * genU n x * incl n

theorem genU2_conjTranspose_mul_self (n : ℕ) {x : Fin (n + 1) → ℂ}
    (hx : x ∈ STW59.unitVectors (Fin (n + 1))) (hN : x (Fin.last n) ≠ -1)
    (hS : x (Fin.last n) ≠ 1) : (genU2 n x)ᴴ * genU2 n x = 1 := by
  refine conjTranspose_mul_self_of_comm (incl_conjTranspose_mul n)
    (genU_conjTranspose_mul_self hx hN hS) ?_
  rw [incl_mul_conjTranspose]
  exact genU_comm_compl hx hN hS

theorem genU2_mul_conjTranspose (n : ℕ) {x : Fin (n + 1) → ℂ}
    (hx : x ∈ STW59.unitVectors (Fin (n + 1))) (hN : x (Fin.last n) ≠ -1)
    (hS : x (Fin.last n) ≠ 1) : genU2 n x * (genU2 n x)ᴴ = 1 :=
  mul_eq_one_comm.mpr (genU2_conjTranspose_mul_self n hx hN hS)

theorem continuous_genU2 (n : ℕ) {X : Type*} [TopologicalSpace X] {ξ : X → Fin (n + 1) → ℂ}
    (hξ : Continuous ξ) (hmem : ∀ s, ξ s ∈ STW59.unitVectors (Fin (n + 1)))
    (hN : ∀ s, ξ s (Fin.last n) ≠ -1) (hS : ∀ s, ξ s (Fin.last n) ≠ 1) :
    Continuous fun s => genU2 n (ξ s) :=
  (continuous_const.matrix_mul (continuous_genU hξ hmem hN hS)).matrix_mul continuous_const

/-! ### The generator as a function on the equatorial space

`Gen.genSphere n` is the composite lane `sp-powers` consumes: radially normalise, embed on
the equator, cut out the `n × n` block.  It is unitary at every `y ≠ 0` and continuous on
`{y | y ≠ 0}`; see the module docstring for why the closed ball is not available. -/

theorem norm_normalise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : E}
    (hy : y ≠ 0) : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

/-- **The generator as a function on `E n`**, radially normalised. -/
def genSphere (n : ℕ) (y : EuclideanSpace ℝ (Fin (2 * n + 1))) : Matrix (Fin n) (Fin n) ℂ :=
  genU2 n (equatorEmb n ((‖y‖⁻¹ : ℝ) • y))

theorem genSphere_conjTranspose_mul_self (n : ℕ)
    {y : EuclideanSpace ℝ (Fin (2 * n + 1))} (hy : y ≠ 0) :
    (genSphere n y)ᴴ * genSphere n y = 1 :=
  genU2_conjTranspose_mul_self n (equatorEmb_mem n (norm_normalise hy))
    (equatorEmb_ne_neg_one n _) (equatorEmb_ne_one n _)

theorem genSphere_mul_conjTranspose (n : ℕ)
    {y : EuclideanSpace ℝ (Fin (2 * n + 1))} (hy : y ≠ 0) :
    genSphere n y * (genSphere n y)ᴴ = 1 :=
  genU2_mul_conjTranspose n (equatorEmb_mem n (norm_normalise hy))
    (equatorEmb_ne_neg_one n _) (equatorEmb_ne_one n _)

/-- **`Gen.genSphere n` is continuous on the punctured space.**  This is the form lane
`sp-powers` states `IsSphereUnitary.continuousOn` against. -/
theorem continuousOn_genSphere (n : ℕ) :
    ContinuousOn (genSphere n) {y : EuclideanSpace ℝ (Fin (2 * n + 1)) | y ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  have hne : ∀ z : {y : EuclideanSpace ℝ (Fin (2 * n + 1)) | y ≠ 0},
      ‖(z : EuclideanSpace ℝ (Fin (2 * n + 1)))‖ ≠ 0 := fun z => norm_ne_zero_iff.mpr z.2
  have hnu : Continuous fun z : {y : EuclideanSpace ℝ (Fin (2 * n + 1)) | y ≠ 0} =>
      (‖(z : EuclideanSpace ℝ (Fin (2 * n + 1)))‖⁻¹ : ℝ) •
        (z : EuclideanSpace ℝ (Fin (2 * n + 1))) :=
    ((continuous_norm.comp continuous_subtype_val).inv₀ hne).smul continuous_subtype_val
  have hxi : Continuous fun z : {y : EuclideanSpace ℝ (Fin (2 * n + 1)) | y ≠ 0} =>
      equatorEmb n ((‖(z : EuclideanSpace ℝ (Fin (2 * n + 1)))‖⁻¹ : ℝ) •
        (z : EuclideanSpace ℝ (Fin (2 * n + 1)))) :=
    (continuous_equatorEmb n).comp hnu
  exact continuous_genU2 n hxi
    (fun z => equatorEmb_mem n (norm_normalise z.2))
    (fun z => equatorEmb_ne_neg_one n _)
    (fun z => equatorEmb_ne_one n _)

/-! ### What is still not here

`Gen.incl n : Matrix (Fin (n+1)) (Fin n) ℂ` onto `pole^⊥`, with
`incl_conjTranspose_mul` and `incl_mul_conjTranspose : incl n * (incl n)ᴴ = 1 - rk1 (ePole n)
(ePole n)`; then `Gen.genU2 n`, the `n × n` block; then

```text
Gen.genSphere n y := Gen.genU2 n (Gen.equatorEmb n (‖y‖⁻¹ • y))
```

which is the interface lane `sp-powers` consumes: continuous and unitary at every `y ≠ 0`.
Two things it needs first and they are a separate piece of work, not a line each: a rank-
generic replacement for `LIXLemmaSixGenerator.conjTranspose_mul_self_of_comm`, which is
currently stated for the concrete `Fin 3`/`Fin 2` isometry, and the `Fin.lastCases`
computation of `incl n * (incl n)ᴴ`.  They are omitted rather than guessed: this file is
the isometry and the equator property, and those are what everything else rests on.
-/

end

end Gen
end LIX
end GroupApproximation
