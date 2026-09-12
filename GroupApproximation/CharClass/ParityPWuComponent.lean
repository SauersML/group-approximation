import GroupApproximation.CharClass.ParityPDecomposable
import GroupApproximation.CharClass.ParityPWuCartan
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# L4a assembled: the diagonal Wu polynomial is a unit times `e_{ip+1}` plus decomposables

Lane `lix-evenside` (successor of `sp-evenside`), `sp-design` §3.3 L4a, universal form.

Over `ℤ`, with `m_{(p^i,1)} = ∑_{|B| = i} ∑_{k ∉ B} (∏_{l ∈ B} X_l^p)·X_k` the right-hand side that
the Cartan half (`ParityPWuCartan.PowerData.p_gamma_succ_eq_smul`) produces, this file proves

```text
  m_{(p^i,1)}  −  c_i·e_{ip+1}   ∈   IsDecomposable e (ip+1),      c_i = (−1)^{i+ip}·(ip+1),
```

and that `c_i` is a unit in any ring where `p = 0`.

The route: `m_{(p^i,1)}` is the degree-`(ip+1)` homogeneous component of `φ_1(e_{i+1})`, where
`φ_1 : y ↦ y + y^p` (`wuComp_eq_wuRHSP`).  Components of symmetric polynomials are symmetric,
and `eCoeff` reads only the component of its own degree (`eCoeff_eq_eCoeff_compSub`), so the
value of `ParityPWuValue.eCoeff_twistSub_esymmSub_succ` is the linear coefficient of
`m_{(p^i,1)}` itself.  Subtracting that multiple of `e_{ip+1}` kills the linear coefficient, and
`ParityPDecomposable.isDecomposable_of_eCoeff_eq_zero` gives the membership.

## Main results

* `ParityP.compSub`, `ParityP.eCoeff_eq_eCoeff_compSub` — homogeneous components in the
  symmetric subalgebra, and the functional `eCoeff` reads one of them.
* `ParityP.wuComp_eq_wuRHSP` — the component is `m_{(p^i,1)}`.
* `ParityP.eCoeff_wuCompSub` — its linear coefficient is `wuCoeff p i = (−1)^{i+ip}·(ip+1)`.
* `ParityP.isDecomposable_wuRHSP` — **L4a, universally**.
* `ParityP.isUnit_wuCoeff_cast` — the leading coefficient is a unit once `p = 0`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

/-! ## 1. Homogeneous components in the symmetric subalgebra -/

section Components

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A homogeneous component of a symmetric polynomial is symmetric: renaming by a permutation
preserves degrees. -/
theorem isSymmetric_homogeneousComponent (m : ℕ) {f : MvPolynomial (Fin n) R}
    (hf : f.IsSymmetric) : (homogeneousComponent m f).IsSymmetric := by
  intro e
  rw [rename_homogeneousComponent, hf e]

/-- The degree-`m` homogeneous component, as an element of the symmetric subalgebra. -/
noncomputable def compSub (m : ℕ) (f : symmetricSubalgebra (Fin n) R) :
    symmetricSubalgebra (Fin n) R :=
  ⟨homogeneousComponent m (f : MvPolynomial (Fin n) R),
    (mem_symmetricSubalgebra _).mpr
      (isSymmetric_homogeneousComponent m ((mem_symmetricSubalgebra _).mp f.2))⟩

theorem compSub_coe (m : ℕ) (f : symmetricSubalgebra (Fin n) R) :
    ((compSub m f : symmetricSubalgebra (Fin n) R) : MvPolynomial (Fin n) R)
      = homogeneousComponent m (f : MvPolynomial (Fin n) R) := rfl

/-- **`eCoeff` reads one homogeneous component.**  The coefficient of `e_{j+1}` depends only on
the degree-`(j+1)` component. -/
theorem eCoeff_eq_eCoeff_compSub (j : Fin n) (f : symmetricSubalgebra (Fin n) R) :
    eCoeff j f = eCoeff j (compSub ((j : ℕ) + 1) f) := by
  have hsum : f = ∑ m ∈ Finset.range ((f : MvPolynomial (Fin n) R).totalDegree + 1),
      compSub m f := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_homogeneousComponent (f : MvPolynomial (Fin n) R)).symm
  conv_lhs => rw [hsum]
  rw [eCoeff_sum, Finset.sum_eq_single ((j : ℕ) + 1)]
  · intro m _ hm
    exact eCoeff_eq_zero_of_degree_ne j (compSub m f)
      (homogeneousComponent_isHomogeneous m (f : MvPolynomial (Fin n) R)) (Ne.symm hm)
  · intro hnot
    have hlt : (f : MvPolynomial (Fin n) R).totalDegree < (j : ℕ) + 1 := by
      by_contra hc
      exact hnot (Finset.mem_range.mpr (by omega))
    have hz : compSub ((j : ℕ) + 1) f = 0 := by
      apply Subtype.ext
      show homogeneousComponent ((j : ℕ) + 1) (f : MvPolynomial (Fin n) R) = 0
      exact homogeneousComponent_eq_zero _ _ hlt
    rw [hz, eCoeff_zero]

/-- `eCoeff` of `C c · g`, with the scalar pulled out. -/
theorem eCoeff_C_mul (j : Fin n) (c : R) (g : symmetricSubalgebra (Fin n) R)
    (hx : C c * (g : MvPolynomial (Fin n) R) ∈ symmetricSubalgebra (Fin n) R) :
    eCoeff j ⟨C c * (g : MvPolynomial (Fin n) R), hx⟩ = c * eCoeff j g := by
  have h : (⟨C c * (g : MvPolynomial (Fin n) R), hx⟩ : symmetricSubalgebra (Fin n) R)
      = c • g := by
    apply Subtype.ext
    rw [Subalgebra.coe_smul, MvPolynomial.smul_eq_C_mul]
  rw [h, eCoeff_smul]

end Components

/-! ## 2. The weight-`(ip+1)` component of the twisted `e_{i+1}` -/

section WuComponent

variable {n : ℕ}

/-- The degree-`(ip+1)` component of `φ_1(e_{i+1})` over `ℤ`, where `φ_1 : y ↦ y + y^p`. -/
noncomputable def wuComp (n p i : ℕ) : MvPolynomial (Fin n) ℤ :=
  homogeneousComponent (i * p + 1) (twist ℤ n p 1 (esymm (Fin n) ℤ (i + 1)))

/-- `wuComp`, as an element of the symmetric subalgebra. -/
noncomputable def wuCompSub (n p i : ℕ) : symmetricSubalgebra (Fin n) ℤ :=
  compSub (i * p + 1) (twistSub p (1 : ℤ) (esymmSub ℤ n (i + 1)))

theorem wuCompSub_coe (p i : ℕ) :
    ((wuCompSub n p i : symmetricSubalgebra (Fin n) ℤ) : MvPolynomial (Fin n) ℤ)
      = wuComp n p i := rfl

/-- The leading coefficient of the diagonal Wu relation over `ℤ`. -/
def wuCoeff (p i : ℕ) : ℤ := (-1) ^ (i + i * p) * ((i * p + 1 : ℕ) : ℤ)

/-- The degree of `(∏_{l ∈ B} X_l^p) · ∏_{l ∈ T \ B} X_l`. -/
theorem isHomogeneous_wuTerm (p : ℕ) (T B : Finset (Fin n)) :
    IsHomogeneous ((∏ l ∈ B, (X l : MvPolynomial (Fin n) ℤ) ^ p) * ∏ l ∈ T \ B, X l)
      (B.card * p + (T \ B).card) := by
  have h1 := IsHomogeneous.prod B (fun l => (X l : MvPolynomial (Fin n) ℤ) ^ p) (fun _ => p)
    fun l _ => isHomogeneous_X_pow l p
  have h2 := IsHomogeneous.prod (T \ B) (fun l => (X l : MvPolynomial (Fin n) ℤ)) (fun _ => 1)
    fun l _ => isHomogeneous_X ℤ l
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1 h2
  exact IsHomogeneous.mul h1 h2

/-- The exponent arithmetic: `ip + 1 = bp + (i + 1 − b)` exactly when `b = i`, for `p ≥ 2` and
`b ≤ i + 1`. -/
theorem wuDeg_eq_iff {p : ℕ} (hp : 2 ≤ p) {i b : ℕ} (hb : b ≤ i + 1) :
    i * p + 1 = b * p + (i + 1 - b) ↔ b = i := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have e1 : i * (q + 1) = i * q + i := by ring
  have e2 : b * (q + 1) = b * q + b := by ring
  rw [e1, e2]
  constructor
  · intro h
    have hbq : b * q = i * q := by omega
    have hqb : q * b = q * i := by rw [Nat.mul_comm q b, Nat.mul_comm q i]; exact hbq
    exact Nat.eq_of_mul_eq_mul_left (by omega) hqb
  · intro h
    subst h
    omega

/-- **The component is `m_{(p^i,1)}`.**  Expanding `∏_{l ∈ T}(X_l^p + X_l)` over the subsets
`B ⊆ T` of factors raised to the `p`-th power, the term indexed by `B` has degree
`|B|·p + |T \ B|`, which is `ip + 1` exactly when `|B| = i`. -/
theorem wuComp_eq_wuRHSP {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    wuComp n p i
      = wuRHSP Finset.univ (fun l : Fin n => (X l : MvPolynomial (Fin n) ℤ) ^ p) X i := by
  rw [wuRHSP_eq_sum_wuMonomialP]
  show homogeneousComponent (i * p + 1) (twist ℤ n p 1 (esymm (Fin n) ℤ (i + 1))) = _
  rw [esymm, map_sum, map_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hcard : T.card = i + 1 := (Finset.mem_powersetCard.mp hT).2
  have hfac : ∀ l ∈ T, twist ℤ n p 1 (X l) = X l ^ p + X l := by
    intro l _
    rw [twist_X, map_one, one_mul, add_comm]
  rw [map_prod, Finset.prod_congr rfl hfac, Finset.prod_add, map_sum, Finset.sum_powerset,
    wuMonomialP_def, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun B hB => ?_
    have hBT := Finset.mem_powersetCard.mp hB
    have hdeg := isHomogeneous_wuTerm p T B
    rw [Finset.card_sdiff_of_subset hBT.1, hcard, hBT.2, Nat.add_sub_cancel_left] at hdeg
    rw [homogeneousComponent_eq_self hdeg]
  · intro b hb hbi
    have hb' : b ≤ i + 1 := by
      have := Finset.mem_range.mp hb
      omega
    refine Finset.sum_eq_zero fun B hB => ?_
    have hBT := Finset.mem_powersetCard.mp hB
    rw [homogeneousComponent_of_mem (isHomogeneous_wuTerm p T B), if_neg]
    rw [Finset.card_sdiff_of_subset hBT.1, hcard, hBT.2]
    intro heq
    exact hbi ((wuDeg_eq_iff hp hb').mp heq)
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-- **The linear coefficient of `m_{(p^i,1)}`** is `wuCoeff p i = (−1)^{i+ip}·(ip+1)`. -/
theorem eCoeff_wuCompSub {p : ℕ} (hp : 2 ≤ p) (i : ℕ) (j : Fin n) (hj : (j : ℕ) = i * p) :
    eCoeff j (wuCompSub n p i) = wuCoeff p i := by
  have h := eCoeff_twistSub_esymmSub_succ (R := ℤ) (n := n) hp 1 i j hj
  rw [eCoeff_eq_eCoeff_compSub, hj, one_pow, mul_one] at h
  exact h

/-- **L4a for the component.** -/
theorem isDecomposable_wuComp {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    IsDecomposable (fun k => esymm (Fin n) ℤ k) (i * p + 1)
      (wuComp n p i - C (wuCoeff p i) * esymm (Fin n) ℤ (i * p + 1)) := by
  have hsym2 : C (wuCoeff p i) * ((esymmSub ℤ n (i * p + 1) : symmetricSubalgebra (Fin n) ℤ) :
      MvPolynomial (Fin n) ℤ) ∈ symmetricSubalgebra (Fin n) ℤ :=
    (mem_symmetricSubalgebra _).mpr
      ((IsSymmetric.C (wuCoeff p i)).mul (esymm_isSymmetric (Fin n) ℤ (i * p + 1)))
  have hhom : IsHomogeneous ((wuCompSub n p i
      - ⟨C (wuCoeff p i) * ((esymmSub ℤ n (i * p + 1) : symmetricSubalgebra (Fin n) ℤ) :
          MvPolynomial (Fin n) ℤ), hsym2⟩ : symmetricSubalgebra (Fin n) ℤ) :
        MvPolynomial (Fin n) ℤ) (i * p + 1) := by
    show IsHomogeneous (wuComp n p i - C (wuCoeff p i) * esymm (Fin n) ℤ (i * p + 1))
      (i * p + 1)
    exact IsHomogeneous.sub (homogeneousComponent_isHomogeneous _ _)
      (IsHomogeneous.C_mul (esymm_isHomogeneous _) _)
  have hlin : ∀ a : Fin n, (a : ℕ) + 1 = i * p + 1 →
      eCoeff a (wuCompSub n p i
        - ⟨C (wuCoeff p i) * ((esymmSub ℤ n (i * p + 1) : symmetricSubalgebra (Fin n) ℤ) :
            MvPolynomial (Fin n) ℤ), hsym2⟩) = 0 := by
    intro a ha
    have ha' : (a : ℕ) = i * p := by omega
    rw [eCoeff_sub, eCoeff_C_mul, eCoeff_wuCompSub hp i a ha', ← ha, eCoeff_esymmSub_self,
      mul_one, sub_self]
  exact isDecomposable_of_eCoeff_eq_zero (by omega) _ hhom hlin

/-- **L4a, universally.**  `m_{(p^i,1)} − wuCoeff p i · e_{ip+1}` is an integral combination of
products of at least two elementary symmetric polynomials of positive index summing to
`ip + 1`. -/
theorem isDecomposable_wuRHSP {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    IsDecomposable (fun k => esymm (Fin n) ℤ k) (i * p + 1)
      (wuRHSP Finset.univ (fun l : Fin n => (X l : MvPolynomial (Fin n) ℤ) ^ p) X i
        - C (wuCoeff p i) * esymm (Fin n) ℤ (i * p + 1)) := by
  rw [← wuComp_eq_wuRHSP hp i]
  exact isDecomposable_wuComp hp i

end WuComponent

/-! ## 3. The leading coefficient is a unit mod `p` -/

section Unit

variable {K : Type*} [CommRing K]

/-- Once `p = 0`, the leading coefficient is the sign `(−1)^{i+ip}`. -/
theorem wuCoeff_cast_eq {p : ℕ} (hpK : (p : K) = 0) (i : ℕ) :
    ((wuCoeff p i : ℤ) : K) = (-1) ^ (i + i * p) := by
  rw [wuCoeff, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_add, Nat.cast_mul, hpK, mul_zero, zero_add, Nat.cast_one, mul_one]

/-- **The leading coefficient is a unit** in any ring where `p = 0`. -/
theorem isUnit_wuCoeff_cast {p : ℕ} (hpK : (p : K) = 0) (i : ℕ) :
    IsUnit ((wuCoeff p i : ℤ) : K) := by
  rw [wuCoeff_cast_eq hpK i]
  exact isUnit_neg_one.pow _

end Unit

end ParityP

end GroupApproximation.CharClass
