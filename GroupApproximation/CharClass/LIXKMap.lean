import GroupApproximation.CharClass.LIXSectionManuscript
import GroupApproximation.Analysis.LIXPowersJoinPower
import GroupApproximation.Meta.AxiomGuard

/-!
# The `k`-fold map `Ψ_k` on `ℂ³`, its `k+1` preimages of `−e₁`, and the rotation

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.2, §1.3.4).

The one-zero Step C of the mod-2 program takes the constant section of the trivial block
to be `e₃` and the transported section to be the tautological point `x` of `S⁵`, so that
the section's single zero sits at `x = −e₃` (`CharClass/LIXSectionManuscript.lean`).
`−e₃` is a suspension point of the clutching coordinate `Re (x 2)`, and a hemisphere
preserving self-map of `S⁵` is a *cone* there, so no `k`-fold map can be a local
homeomorphism at it.  The strengthening therefore moves the constant section to `e₁`,
whose antipode lies on the **equator** `{Re (x 2) = 0}`, and replaces `x` by `Ψ_k ∘ x`.

## The map

`sp-design` §2.1 and `sp-powers` §0 agreed, independently, on one `Ψ_k`: keep the modulus
of the first complex coordinate, multiply its argument by `k + 1`, fix everything else.
The scalar half of that map is `sp-powers`' `Powers.joinC k z = (‖z‖ ^ k)⁻¹ · z ^ (k+1)`,
and this file uses **their** `joinC` rather than a second spelling of it.  Their
`Powers.joinPow`, which packages the same map as an `IsRadialMap`, is *not* usable here:
it is built from `Powers.planeSub`, which needs `InnerProductSpace ℝ E`, and `S⁵` in this
tree is `STW59.unitVectors (Fin 3) ⊆ (Fin 3 → ℂ)`, a sup-normed pi type with no such
instance.  `psiVec` below is the same map written in the coordinates this side of the tree
uses, and the only thing it borrows is the scalar formula.

The index is `sp-powers`' shifted one: `psiVec k` is the map of degree `k + 1`, so `k = 0`
is the identity and no `1 ≤ k` side condition is ever carried.  The exponent that appears
in the theorem is `k + 1`.

## The `k+1` zeros

`Ψ_k x = −e₁` forces the last two coordinates to vanish and `x₀ ^ (k+1) = −1`; the modulus
is then free, because `‖joinC k z‖ = ‖z‖` already pins `‖x₀‖ = 1`.  So the preimage is the
set of `(k+1)`-st roots of `−1` on the `e₁`-axis, which Mathlib enumerates for us:
`IsPrimitiveRoot.nthRoots_eq` writes them as `ζ^j · α` for `ζ` a primitive `(k+1)`-st root
of unity and `α` any one solution, and `IsPrimitiveRoot.injOn_pow_mul` says the `k+1`
of them are distinct.  All lie on the equator, because their last coordinate is `0`.

## The rotation

`kRot k m` multiplies the first coordinate by `ζ^m`.  It preserves every coordinate's
modulus, satisfies `Ψ_k ∘ kRot k m = Ψ_k`, and carries the zero `z₀` to the zero `z_j`
when `m = j`.  That is the whole of `sp-design` §4.1's Half A input: the `k+1` zeros are
one free orbit of a rotation that is *linear*, so it extends to a homeomorphism of the
ambient space and is isotopic to the identity through `kRot` at fractional exponents.

## Main results

* `eOne`, `negEOne` — the constant section and its antipode, on the equator.
* `psiVec`, `norm_psiVec_apply`, `continuous_psiVec` — the map.
* `kRoot`, `kRoot_pow`, `kRoot_injective`, `exists_kRoot_of_pow_eq_neg_one` — the `k+1`
  roots of `−1`.
* `kZero`, `kZero_injective` — the `k+1` zeros as points of `S⁵`.
* `psiVec_eq_neg_eOne_iff` — **the zero locus**: `Ψ_k x = −e₁` iff `x` is one of them.
* `psiVec_kRot`, `kRot_kZeroVec_zero` — the rotation and the free orbit.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59
open GroupApproximation.LIX.Powers

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## 1. The constant section moves to `e₁` -/

/-- `e₁`, the strengthened program's constant section of the trivial block.  Unlike `e₃`
it satisfies `Re (e₁ 2) = 0`, so `±e₁` lie on the equator `S⁴ = {Re (x 2) = 0}` and are
*not* suspension points of the clutching coordinate. -/
def eOne : Fin 3 → ℂ := Pi.single 0 1

theorem eOne_normSq : ∑ i, ‖eOne i‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_three]
  simp [eOne]

theorem eOne_ne_zero : eOne ≠ 0 := by
  intro h
  have h0 : eOne 0 = 0 := by rw [h]; rfl
  rw [eOne, Pi.single_eq_same] at h0
  exact one_ne_zero h0

/-- `−e₁` is on the equator: its clutching coordinate is zero. -/
theorem re_neg_eOne_two : ((-eOne) 2).re = 0 := by
  simp [eOne]

/-- The point of `S⁵` antipodal to `e₁`.  At `k = 0` this is the single zero. -/
def negEOne : ↥(unitVectors (Fin 3)) :=
  ⟨fun i => -eOne i, by
    rw [mem_unitVectors_iff]
    simpa using eOne_normSq⟩

/-! ## 2. Two scalar facts about moduli -/

/-- A complex number whose modulus has a positive power equal to `1` has modulus `1`. -/
theorem norm_eq_one_of_norm_pow {z : ℂ} {k : ℕ} (h : ‖z‖ ^ (k + 1) = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ^ (k + 1) = (1 : ℝ) ^ (k + 1) := by rw [one_pow]; exact h
  exact (pow_left_inj₀ (norm_nonneg z) zero_le_one (Nat.succ_ne_zero k)).mp h1

theorem norm_eq_one_of_pow_eq_neg_one {z : ℂ} {k : ℕ} (h : z ^ (k + 1) = -1) : ‖z‖ = 1 := by
  refine norm_eq_one_of_norm_pow (k := k) ?_
  rw [← norm_pow, h, norm_neg, norm_one]

theorem norm_eq_one_of_pow_eq_one {z : ℂ} {k : ℕ} (h : z ^ (k + 1) = 1) : ‖z‖ = 1 := by
  refine norm_eq_one_of_norm_pow (k := k) ?_
  rw [← norm_pow, h, norm_one]

/-- **On the unit circle the join power is the plain power.**  This is the only place the
renormalising factor `(‖z‖^k)⁻¹` of `Powers.joinC` is ever discharged. -/
theorem joinC_eq_pow_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) :
    joinC k z = z ^ (k + 1) := by
  rw [joinC, hz, one_pow, Complex.ofReal_one, inv_one, one_mul]

/-- **`joinC k z = −1` is exactly `z^{k+1} = −1`.**  Neither direction assumes `‖z‖ = 1`:
the forward one gets it from `norm_joinC`, the backward one from the equation itself. -/
theorem joinC_eq_neg_one_iff (k : ℕ) (z : ℂ) : joinC k z = -1 ↔ z ^ (k + 1) = -1 := by
  constructor
  · intro h
    have hz : ‖z‖ = 1 := by
      have hn := norm_joinC k z
      rw [h] at hn
      simpa using hn.symm
    rw [← joinC_eq_pow_of_norm_one hz k, h]
  · intro h
    rw [joinC_eq_pow_of_norm_one (norm_eq_one_of_pow_eq_neg_one h) k, h]

/-! ## 3. The map `Ψ_k` on `ℂ³` -/

/-- **The `k`-fold map**, in the coordinates of `unitVectors (Fin 3)`: apply `sp-powers`'
scalar join power to the first coordinate and leave the other two alone.  It preserves
every coordinate's modulus, hence the Hermitian norm *and* the sup norm, hence both the
sphere and the equator `{Re (x 2) = 0}`. -/
def psiVec (k : ℕ) (x : Fin 3 → ℂ) : Fin 3 → ℂ := Function.update x 0 (joinC k (x 0))

@[simp] theorem psiVec_apply_zero (k : ℕ) (x : Fin 3 → ℂ) :
    psiVec k x 0 = joinC k (x 0) :=
  Function.update_self _ _ _

theorem psiVec_apply_of_ne (k : ℕ) (x : Fin 3 → ℂ) {i : Fin 3} (hi : i ≠ 0) :
    psiVec k x i = x i :=
  Function.update_of_ne hi _ _

@[simp] theorem psiVec_apply_one (k : ℕ) (x : Fin 3 → ℂ) : psiVec k x 1 = x 1 :=
  psiVec_apply_of_ne k x (by decide)

@[simp] theorem psiVec_apply_two (k : ℕ) (x : Fin 3 → ℂ) : psiVec k x 2 = x 2 :=
  psiVec_apply_of_ne k x (by decide)

/-- **`Ψ_k` preserves every coordinate's modulus.** -/
theorem norm_psiVec_apply (k : ℕ) (x : Fin 3 → ℂ) (i : Fin 3) :
    ‖psiVec k x i‖ = ‖x i‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiVec_apply_zero, norm_joinC]
  · rw [psiVec_apply_of_ne k x hi]

/-- **`Ψ_k` preserves the Hermitian norm**, so it maps `S⁵` to `S⁵`. -/
theorem normSq_psiVec (k : ℕ) (x : Fin 3 → ℂ) :
    ∑ i, ‖psiVec k x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Finset.sum_congr rfl fun i _ => by rw [norm_psiVec_apply]

theorem psiVec_mem_unitVectors {k : ℕ} {x : Fin 3 → ℂ} (hx : x ∈ unitVectors (Fin 3)) :
    psiVec k x ∈ unitVectors (Fin 3) := by
  rw [mem_unitVectors_iff, normSq_psiVec]
  exact mem_unitVectors_iff.mp hx

theorem continuous_psiVec (k : ℕ) : Continuous (psiVec k) := by
  refine continuous_pi fun i => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [psiVec_apply_zero]
    exact (continuous_joinC k).comp (continuous_apply 0)
  · simp only [psiVec_apply_of_ne _ _ hi]
    exact continuous_apply i

/-- At `k = 0` the map is the identity, so the one-zero geometry is the `k = 0` case of
the `k`-zero geometry and nothing is duplicated. -/
theorem psiVec_zero_eq (x : Fin 3 → ℂ) : psiVec 0 x = x := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiVec_apply_zero, joinC_id]
  · rw [psiVec_apply_of_ne _ _ hi]

/-! ## 4. The `k+1` roots of `−1` -/

/-- A primitive `(k+1)`-st root of unity. -/
def kUnity (k : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((k + 1 : ℕ) : ℂ))

theorem isPrimitiveRoot_kUnity (k : ℕ) : IsPrimitiveRoot (kUnity k) (k + 1) :=
  Complex.isPrimitiveRoot_exp (k + 1) (Nat.succ_ne_zero k)

theorem kUnity_pow (k : ℕ) : kUnity k ^ (k + 1) = 1 :=
  (isPrimitiveRoot_kUnity k).pow_eq_one

theorem norm_kUnity (k : ℕ) : ‖kUnity k‖ = 1 :=
  norm_eq_one_of_pow_eq_one (kUnity_pow k)

/-- One fixed `(k+1)`-st root of `−1`. -/
def kBase (k : ℕ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I / ((k + 1 : ℕ) : ℂ))

theorem kBase_ne_zero (k : ℕ) : kBase k ≠ 0 := Complex.exp_ne_zero _

theorem kBase_pow (k : ℕ) : kBase k ^ (k + 1) = -1 := by
  have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  rw [kBase, ← Complex.exp_nat_mul]
  rw [show ((k + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / ((k + 1 : ℕ) : ℂ))
      = (Real.pi : ℂ) * Complex.I by field_simp]
  exact Complex.exp_pi_mul_I

/-- **The `k+1` solutions of `z^{k+1} = −1`**, indexed by `Fin (k+1)`. -/
def kRoot (k : ℕ) (j : Fin (k + 1)) : ℂ := kUnity k ^ (j : ℕ) * kBase k

theorem kRoot_pow (k : ℕ) (j : Fin (k + 1)) : kRoot k j ^ (k + 1) = -1 := by
  rw [kRoot, mul_pow, ← pow_mul, mul_comm (j : ℕ) (k + 1), pow_mul, kUnity_pow, one_pow,
    one_mul, kBase_pow]

theorem norm_kRoot (k : ℕ) (j : Fin (k + 1)) : ‖kRoot k j‖ = 1 :=
  norm_eq_one_of_pow_eq_neg_one (kRoot_pow k j)

theorem kRoot_ne_zero (k : ℕ) (j : Fin (k + 1)) : kRoot k j ≠ 0 := by
  intro h
  have := norm_kRoot k j
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **The `k+1` roots are distinct.**  Mathlib's `injOn_pow_mul` for a primitive root. -/
theorem kRoot_injective (k : ℕ) : Function.Injective (kRoot k) := by
  intro a b hab
  have hinj := (isPrimitiveRoot_kUnity k).injOn_pow_mul (kBase_ne_zero k)
  have ha : (a : ℕ) ∈ (Finset.range (k + 1) : Set ℕ) := by
    simpa using a.isLt
  have hb : (b : ℕ) ∈ (Finset.range (k + 1) : Set ℕ) := by
    simpa using b.isLt
  exact Fin.val_injective (hinj ha hb hab)

/-- **There are no other roots.**  From `IsPrimitiveRoot.nthRoots_eq`, which enumerates
the roots of `X^n − a` as `ζ^i · α`. -/
theorem exists_kRoot_of_pow_eq_neg_one {k : ℕ} {z : ℂ} (h : z ^ (k + 1) = -1) :
    ∃ j : Fin (k + 1), z = kRoot k j := by
  have hmem : z ∈ Polynomial.nthRoots (k + 1) (-1 : ℂ) :=
    (Polynomial.mem_nthRoots (Nat.succ_pos k)).mpr h
  rw [(isPrimitiveRoot_kUnity k).nthRoots_eq (kBase_pow k)] at hmem
  obtain ⟨m, hm, hmz⟩ := Multiset.mem_map.mp hmem
  exact ⟨⟨m, Multiset.mem_range.mp hm⟩, hmz.symm⟩

/-! ## 5. The `k+1` zeros, as points of `S⁵` -/

/-- The `j`-th zero, as a vector: `ζ_j · e₁`. -/
def kZeroVec (k : ℕ) (j : Fin (k + 1)) : Fin 3 → ℂ := Pi.single 0 (kRoot k j)

@[simp] theorem kZeroVec_apply_zero (k : ℕ) (j : Fin (k + 1)) :
    kZeroVec k j 0 = kRoot k j :=
  Pi.single_eq_same _ _

@[simp] theorem kZeroVec_apply_one (k : ℕ) (j : Fin (k + 1)) : kZeroVec k j 1 = 0 := by
  simp [kZeroVec]

@[simp] theorem kZeroVec_apply_two (k : ℕ) (j : Fin (k + 1)) : kZeroVec k j 2 = 0 := by
  simp [kZeroVec]

theorem kZeroVec_mem (k : ℕ) (j : Fin (k + 1)) :
    kZeroVec k j ∈ unitVectors (Fin 3) := by
  rw [mem_unitVectors_iff, Fin.sum_univ_three, kZeroVec_apply_zero, kZeroVec_apply_one,
    kZeroVec_apply_two, norm_kRoot, norm_zero]
  norm_num

/-- **The `j`-th zero lies on the equator.**  Its clutching coordinate is `0`, so no zero
of the `k`-fold section is a suspension point — which is the whole reason the constant
section had to move from `e₃` to `e₁`. -/
theorem re_kZeroVec_two (k : ℕ) (j : Fin (k + 1)) : (kZeroVec k j 2).re = 0 := by
  rw [kZeroVec_apply_two]
  simp

/-- The `j`-th zero, as a point of `S⁵`. -/
def kZero (k : ℕ) (j : Fin (k + 1)) : ↥(unitVectors (Fin 3)) :=
  ⟨kZeroVec k j, kZeroVec_mem k j⟩

theorem kZero_injective (k : ℕ) : Function.Injective (kZero k) := by
  intro a b hab
  have h : kZeroVec k a 0 = kZeroVec k b 0 := by
    rw [show kZeroVec k a = kZeroVec k b from congrArg Subtype.val hab]
  exact kRoot_injective k (by rwa [kZeroVec_apply_zero, kZeroVec_apply_zero] at h)

/-! ## 6. The zero locus -/

/-- **The zero locus of the trivial block.**  `Ψ_k x = −e₁` exactly at the `k+1` points
`ζ_j e₁` with `ζ_j^{k+1} = −1`.

This is the only geometric input the `k`-zero Step C needs from the map: everything else
is the one-zero argument transported around the rotation orbit. -/
theorem psiVec_eq_neg_eOne_iff (k : ℕ) (x : Fin 3 → ℂ) :
    psiVec k x = -eOne ↔ ∃ j : Fin (k + 1), x = kZeroVec k j := by
  constructor
  · intro h
    have h0 : joinC k (x 0) = -1 := by
      have hc := congrFun h 0
      rw [psiVec_apply_zero] at hc
      rw [hc]
      simp [eOne]
    have h1 : x 1 = 0 := by
      have hc := congrFun h 1
      rw [psiVec_apply_one] at hc
      rw [hc]
      simp [eOne]
    have h2 : x 2 = 0 := by
      have hc := congrFun h 2
      rw [psiVec_apply_two] at hc
      rw [hc]
      simp [eOne]
    obtain ⟨j, hj⟩ := exists_kRoot_of_pow_eq_neg_one ((joinC_eq_neg_one_iff k (x 0)).mp h0)
    refine ⟨j, funext fun i => ?_⟩
    fin_cases i
    · simpa using hj
    · simpa using h1
    · simpa using h2
  · rintro ⟨j, rfl⟩
    funext i
    fin_cases i
    · simp [eOne, joinC_eq_pow_of_norm_one (norm_kRoot k j) k, kRoot_pow]
    · simp [eOne]
    · simp [eOne]

/-! ## 7. The rotation, and the free orbit -/

/-- **The rotation of order `k+1`** in the `e₁`-plane, at exponent `m`.  It is the
restriction of a *linear* unitary of `ℂ³`, so it is a homeomorphism of the sphere and of
the equator, and `kRot k m` for `m` running through `0, …, k` is the isotopy that
`sp-design` §4.1 Half A uses. -/
def kRot (k : ℕ) (m : ℕ) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  Function.update x 0 (kUnity k ^ m * x 0)

@[simp] theorem kRot_apply_zero (k m : ℕ) (x : Fin 3 → ℂ) :
    kRot k m x 0 = kUnity k ^ m * x 0 :=
  Function.update_self _ _ _

theorem kRot_apply_of_ne (k m : ℕ) (x : Fin 3 → ℂ) {i : Fin 3} (hi : i ≠ 0) :
    kRot k m x i = x i :=
  Function.update_of_ne hi _ _

theorem norm_kRot_apply (k m : ℕ) (x : Fin 3 → ℂ) (i : Fin 3) :
    ‖kRot k m x i‖ = ‖x i‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rw [kRot_apply_zero, norm_mul, norm_pow, norm_kUnity, one_pow, one_mul]
  · rw [kRot_apply_of_ne k m x hi]

theorem kRot_mem_unitVectors {k m : ℕ} {x : Fin 3 → ℂ} (hx : x ∈ unitVectors (Fin 3)) :
    kRot k m x ∈ unitVectors (Fin 3) := by
  rw [mem_unitVectors_iff, ← mem_unitVectors_iff.mp hx]
  exact Finset.sum_congr rfl fun i _ => by rw [norm_kRot_apply]

theorem continuous_kRot (k m : ℕ) : Continuous (kRot k m) := by
  refine continuous_pi fun i => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [kRot_apply_zero]
    exact continuous_const.mul (continuous_apply 0)
  · simp only [kRot_apply_of_ne _ _ _ hi]
    exact continuous_apply i

/-- The scalar half of the rotation invariance: multiplying by a power of `ζ` changes
neither the modulus nor the `(k+1)`-st power. -/
theorem joinC_kUnity_pow_mul (k m : ℕ) (z : ℂ) :
    joinC k (kUnity k ^ m * z) = joinC k z := by
  have hnorm : ‖kUnity k ^ m * z‖ = ‖z‖ := by
    rw [norm_mul, norm_pow, norm_kUnity, one_pow, one_mul]
  have hpow : (kUnity k ^ m * z) ^ (k + 1) = z ^ (k + 1) := by
    rw [mul_pow, ← pow_mul, mul_comm m (k + 1), pow_mul, kUnity_pow, one_pow, one_mul]
  rw [joinC, joinC, hnorm, hpow]

/-- **`Ψ_k` is invariant under the rotation.**  This, and not any degree computation, is
what makes every local contribution of the `k`-zero Step C literally equal. -/
theorem psiVec_kRot (k m : ℕ) (x : Fin 3 → ℂ) : psiVec k (kRot k m x) = psiVec k x := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiVec_apply_zero, psiVec_apply_zero, kRot_apply_zero, joinC_kUnity_pow_mul]
  · rw [psiVec_apply_of_ne _ _ hi, psiVec_apply_of_ne _ _ hi, kRot_apply_of_ne _ _ _ hi]

/-- **The `k+1` zeros form one free orbit of the rotation**, based at the zeroth.  This is
the statement `sp-design` §4.1 Half A consumes: the homeomorphism `kRot k j` of the
ambient space carries `z₀` to `z_j`. -/
theorem kRot_kZeroVec_zero (k : ℕ) (j : Fin (k + 1)) :
    kRot k (j : ℕ) (kZeroVec k 0) = kZeroVec k j := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · simp [kRoot]
  · rw [kRot_apply_of_ne _ _ _ hi]
    simp [kZeroVec, hi]

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the build**
if it leaves the classical allowlist. -/

#audit_axioms psiVec_eq_neg_eOne_iff
#audit_axioms kRoot_injective
#audit_axioms psiVec_kRot

end GroupApproximation.CharClass
