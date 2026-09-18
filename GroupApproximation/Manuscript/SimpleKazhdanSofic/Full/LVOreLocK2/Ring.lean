import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.YaoGeneration
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.NKAugmentation

/-!
# The skew Laurent ring as the localization of `S[t;φ]` at the powers of `t` (lane LVOreLocK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; work order
WO-LVK2Route-1 (Core-A).  Core-A has to show that `K₂(S[t;φ]) → K₂(S[t,t⁻¹;φ])` is onto for an
ultramatricial `𝔽₂`-ring `S`.  The source argument (Quillen, *Higher algebraic K-theory I*,
§5 Thm 5 and §7; Grayson, *K-theory of localizations*; Ara–Brustenga–Cortiñas 2009, `yaoseq6.tex`
l.574-640) runs the localization sequence of the Ore set `{tⁿ}` in `R₊ = S[t;φ]`:
`K₂(R₊) → K₂(R₊[t⁻¹]) → K₁(H_t) → K₁(R₊)`, with `H_t` the `t`-torsion modules of projective
dimension one.  This file proves the ring-theoretic hypotheses of that sequence for
`R₊ = skewHalf S 1 ⊆ Λ = SkewLaurent S`:

* `tPow_add`, `tPow_zero`, `isUnit_tPow`: `t^m` are units of `Λ`, `t^{m+n} = t^m t^n`;
* `single_eq_constMap_mul_tPow`, `tPow_mul_constMap`: `s t^m = s · t^m`, `t^m s = φ^m(s) t^m`;
* `skewHalf_one_eq_halfSupport`: `S[t;φ]` is exactly the set of series in degrees `≥ 0`;
* `conj_tPow_mem_skewHalf_one`: `t^m R₊ t^{-m} ⊆ R₊`, hence `t^m R₊ = R₊ t^m` (`t` is normal);
* `tPow_mul_left_cancel`, `mul_tPow_right_cancel`: `t` is regular;
* `exists_eq_mul_tPow_neg`, `exists_eq_tPow_neg_mul`: `Λ = R₊[t⁻¹]` on both sides
  (every `f ∈ Λ` is `r t^{-N}` and `t^{-N} r'` with `r, r' ∈ R₊`);
* `exists_eq_tPow_one_mul_of_coeff_one_eq_zero`: the kernel of the augmentation `R₊ → S` is
  `t R₊ = R₊ t`, so `R₊ / t R₊ = S`.
-/

namespace GroupApproximation.Full.LVOreLocK2

open GroupApproximation.Full.LVSkewLaurentK2

section Monomials

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- `t⁰ = 1`.  (Quillen localization for `{tⁿ}`; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem tPow_zero : tPow S 0 = 1 := by
  rw [tPow, ofAdd_zero, SkewMonoidAlgebra.single_one_one]

/-- `t^{m+n} = t^m t^n`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem tPow_add (m n : ℤ) : tPow S (m + n) = tPow S m * tPow S n :=
  (single_mul_tPow m n (1 : S)).symm

/-- `t^m t^{-m} = 1`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem tPow_mul_tPow_neg (m : ℤ) : tPow S m * tPow S (-m) = 1 := by
  rw [← tPow_add, add_neg_cancel, tPow_zero]

/-- `t^{-m} t^m = 1`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem tPow_neg_mul_tPow (m : ℤ) : tPow S (-m) * tPow S m = 1 := by
  rw [← tPow_add, neg_add_cancel, tPow_zero]

/-- The powers of `t` are units of the Laurent ring.  (Quillen localization for `{tⁿ}`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem isUnit_tPow (m : ℤ) : IsUnit (tPow S m) :=
  ⟨⟨tPow S m, tPow S (-m), tPow_mul_tPow_neg m, tPow_neg_mul_tPow m⟩, rfl⟩

/-- `s t^m = s · t^m`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem single_eq_constMap_mul_tPow (m : ℤ) (a : S) :
    (SkewMonoidAlgebra.single (Multiplicative.ofAdd m) a : SkewLaurent S) =
      constMap S a * tPow S m := by
  change _ = SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a *
    SkewMonoidAlgebra.single (Multiplicative.ofAdd m) (1 : S)
  rw [SkewMonoidAlgebra.single_mul_single, one_mul, one_smul, mul_one]

/-- `t^m · s t^n = φ^m(s) t^{m+n}`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem tPow_mul_single (m n : ℤ) (a : S) :
    tPow S m * (SkewMonoidAlgebra.single (Multiplicative.ofAdd n) a : SkewLaurent S) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (m + n)) (Multiplicative.ofAdd m • a) := by
  rw [tPow, SkewMonoidAlgebra.single_mul_single, one_mul, ofAdd_add]

/-- The commutation rule `t^m s = φ^m(s) t^m`.  (`yaoseq6.tex` `thm:skewyao`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem tPow_mul_constMap (m : ℤ) (a : S) :
    tPow S m * constMap S a = constMap S (Multiplicative.ofAdd m • a) * tPow S m := by
  rw [← single_eq_constMap_mul_tPow]
  change SkewMonoidAlgebra.single (Multiplicative.ofAdd m) (1 : S) *
    SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a = _
  rw [SkewMonoidAlgebra.single_mul_single, mul_one, one_mul]

/-- `t` is left regular: `t^m x = t^m y → x = y`.  (Quillen localization, the Ore set consists of
non-zero-divisors; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem tPow_mul_left_cancel (m : ℤ) {x y : SkewLaurent S} (h : tPow S m * x = tPow S m * y) :
    x = y :=
  calc x = tPow S (-m) * (tPow S m * x) := by rw [← mul_assoc, tPow_neg_mul_tPow, one_mul]
    _ = tPow S (-m) * (tPow S m * y) := by rw [h]
    _ = y := by rw [← mul_assoc, tPow_neg_mul_tPow, one_mul]

/-- `t` is right regular: `x t^m = y t^m → x = y`.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem mul_tPow_right_cancel (m : ℤ) {x y : SkewLaurent S} (h : x * tPow S m = y * tPow S m) :
    x = y :=
  calc x = x * tPow S m * tPow S (-m) := by rw [mul_assoc, tPow_mul_tPow_neg, mul_one]
    _ = y * tPow S m * tPow S (-m) := by rw [h]
    _ = y := by rw [mul_assoc, tPow_mul_tPow_neg, mul_one]

/-- `t^k ∈ S[t;φ]` for `k : ℕ`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem tPow_natCast_mem_skewHalf_one (k : ℕ) : tPow S (k : ℤ) ∈ skewHalf S 1 := by
  have h := single_natMul_mem_skewHalf (S := S) 1 (1 : S) k
  rw [mul_one] at h
  exact h

end Monomials

section HalfRing

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- **`S[t;φ]` is the ring of series in nonnegative degrees**: every Laurent series without
coefficients in negative degrees lies in the subring generated by the constants and `t`.
(`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem halfSupport_one_le_skewHalf : halfSupport S 1 ≤ skewHalf S 1 := by
  intro f hf
  have hf' := (mem_halfSupport S).mp hf
  rw [← SkewMonoidAlgebra.sum_single f, SkewMonoidAlgebra.sum_def']
  refine Subring.sum_mem _ fun g hg => ?_
  have h0 : 0 ≤ Multiplicative.toAdd g := by
    by_contra hneg
    exact SkewMonoidAlgebra.mem_support_iff.mp hg (hf' g (by omega))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) * 1 = Multiplicative.toAdd g :=
    ⟨(Multiplicative.toAdd g).toNat, by omega⟩
  have hm := single_natMul_mem_skewHalf (S := S) 1 (SkewMonoidAlgebra.coeff f g) n
  rw [hn, ofAdd_toAdd] at hm
  exact hm

/-- `S[t;φ] = {f ∈ S[t,t⁻¹;φ] : f has no coefficients in negative degrees}`.
(`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem skewHalf_one_eq_halfSupport : skewHalf S 1 = halfSupport S 1 :=
  le_antisymm (skewHalf_le_halfSupport S 1) halfSupport_one_le_skewHalf

/-- **Denominators on the right.**  For every `f ∈ S[t,t⁻¹;φ]` there is `N` with
`f t^k ∈ S[t;φ]` for all `k ≥ N`.  (Quillen localization: `Λ = R₊[t⁻¹]`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_forall_mul_tPow_mem (f : SkewLaurent S) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f * tPow S (k : ℤ) ∈ skewHalf S 1 := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => exact ⟨0, fun _ _ => by rw [zero_mul]; exact (skewHalf S 1).zero_mem⟩
  | single g a =>
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, Multiplicative.ofAdd m = g := ⟨_, ofAdd_toAdd g⟩
    refine ⟨(-m).toNat, fun k hk => ?_⟩
    rw [single_mul_tPow]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) * 1 = m + (k : ℤ) := ⟨(m + (k : ℤ)).toNat, by omega⟩
    have hm := single_natMul_mem_skewHalf (S := S) 1 a n
    rw [hn] at hm
    exact hm
  | add _ _ h₁ h₂ =>
    obtain ⟨N₁, hN₁⟩ := h₁
    obtain ⟨N₂, hN₂⟩ := h₂
    refine ⟨max N₁ N₂, fun k hk => ?_⟩
    rw [add_mul]
    exact (skewHalf S 1).add_mem (hN₁ k (le_trans (le_max_left _ _) hk))
      (hN₂ k (le_trans (le_max_right _ _) hk))

/-- **Denominators on the left.**  For every `f ∈ S[t,t⁻¹;φ]` there is `N` with
`t^k f ∈ S[t;φ]` for all `k ≥ N`.  (Quillen localization: `Λ = R₊[t⁻¹]`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_forall_tPow_mul_mem (f : SkewLaurent S) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → tPow S (k : ℤ) * f ∈ skewHalf S 1 := by
  induction f using SkewMonoidAlgebra.induction_on with
  | zero => exact ⟨0, fun _ _ => by rw [mul_zero]; exact (skewHalf S 1).zero_mem⟩
  | single g a =>
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, Multiplicative.ofAdd m = g := ⟨_, ofAdd_toAdd g⟩
    refine ⟨(-m).toNat, fun k hk => ?_⟩
    rw [tPow_mul_single]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) * 1 = (k : ℤ) + m := ⟨((k : ℤ) + m).toNat, by omega⟩
    have hm := single_natMul_mem_skewHalf (S := S) 1 (Multiplicative.ofAdd (k : ℤ) • a) n
    rw [hn] at hm
    exact hm
  | add _ _ h₁ h₂ =>
    obtain ⟨N₁, hN₁⟩ := h₁
    obtain ⟨N₂, hN₂⟩ := h₂
    refine ⟨max N₁ N₂, fun k hk => ?_⟩
    rw [mul_add]
    exact (skewHalf S 1).add_mem (hN₁ k (le_trans (le_max_left _ _) hk))
      (hN₂ k (le_trans (le_max_right _ _) hk))

/-- `Λ = R₊[t⁻¹]` (right fractions): every `f` is `r t^{-N}` with `r ∈ S[t;φ]`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_eq_mul_tPow_neg (f : SkewLaurent S) :
    ∃ N : ℕ, ∃ r ∈ skewHalf S 1, f = r * tPow S (-(N : ℤ)) := by
  obtain ⟨N, hN⟩ := exists_forall_mul_tPow_mem f
  exact ⟨N, f * tPow S (N : ℤ), hN N le_rfl, by rw [mul_assoc, tPow_mul_tPow_neg, mul_one]⟩

/-- `Λ = R₊[t⁻¹]` (left fractions): every `f` is `t^{-N} r` with `r ∈ S[t;φ]`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_eq_tPow_neg_mul (f : SkewLaurent S) :
    ∃ N : ℕ, ∃ r ∈ skewHalf S 1, f = tPow S (-(N : ℤ)) * r := by
  obtain ⟨N, hN⟩ := exists_forall_tPow_mul_mem f
  exact ⟨N, tPow S (N : ℤ) * f, hN N le_rfl, by rw [← mul_assoc, tPow_neg_mul_tPow, one_mul]⟩

end HalfRing

section Normal

variable (S : Type*) [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- The Laurent series whose conjugate by `t^m` lies in `S[t;φ]`, as a subring.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def conjHalf (m : ℤ) : Subring (SkewLaurent S) where
  carrier := {x | tPow S m * x * tPow S (-m) ∈ skewHalf S 1}
  mul_mem' := fun {x y} hx hy => by
    change tPow S m * (x * y) * tPow S (-m) ∈ skewHalf S 1
    have e : tPow S m * (x * y) * tPow S (-m) =
        (tPow S m * x * tPow S (-m)) * (tPow S m * y * tPow S (-m)) := by
      rw [show (tPow S m * x * tPow S (-m)) * (tPow S m * y * tPow S (-m)) =
          tPow S m * x * (tPow S (-m) * tPow S m) * y * tPow S (-m) by simp only [mul_assoc],
        tPow_neg_mul_tPow, mul_one, mul_assoc (tPow S m) x y]
    rw [e]
    exact (skewHalf S 1).mul_mem hx hy
  one_mem' := by
    change tPow S m * 1 * tPow S (-m) ∈ skewHalf S 1
    rw [mul_one, tPow_mul_tPow_neg]
    exact (skewHalf S 1).one_mem
  add_mem' := fun {x y} hx hy => by
    change tPow S m * (x + y) * tPow S (-m) ∈ skewHalf S 1
    rw [mul_add, add_mul]
    exact (skewHalf S 1).add_mem hx hy
  zero_mem' := by
    change tPow S m * 0 * tPow S (-m) ∈ skewHalf S 1
    rw [mul_zero, zero_mul]
    exact (skewHalf S 1).zero_mem
  neg_mem' := fun {x} hx => by
    change tPow S m * (-x) * tPow S (-m) ∈ skewHalf S 1
    rw [mul_neg, neg_mul]
    exact (skewHalf S 1).neg_mem hx

variable {S}

/-- **`t` is normal in `S[t;φ]`**: conjugation by `t^m` preserves `S[t;φ]`, since it fixes `t` and
sends the constant `s` to `φ^m(s)`.  (Quillen localization for a normal element;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem conj_tPow_mem_skewHalf_one (m : ℤ) {x : SkewLaurent S} (hx : x ∈ skewHalf S 1) :
    tPow S m * x * tPow S (-m) ∈ skewHalf S 1 := by
  have hle : skewHalf S 1 ≤ conjHalf S m := by
    refine Subring.closure_le.mpr (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      change tPow S m * constMap S a * tPow S (-m) ∈ skewHalf S 1
      rw [tPow_mul_constMap, mul_assoc, tPow_mul_tPow_neg, mul_one]
      exact constMap_mem_skewHalf S 1 _
    · rintro _ rfl
      change tPow S m * tPow S 1 * tPow S (-m) ∈ skewHalf S 1
      rw [← tPow_add, ← tPow_add, show m + 1 + -m = (1 : ℤ) by omega]
      exact tPow_mem_skewHalf 1
  exact hle hx

/-- `t^m x = (t^m x t^{-m}) t^m`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem tPow_mul_eq_conj_mul (m : ℤ) (x : SkewLaurent S) :
    tPow S m * x = (tPow S m * x * tPow S (-m)) * tPow S m := by
  rw [mul_assoc (tPow S m * x), tPow_neg_mul_tPow, mul_one]

/-- `t^m R₊ ⊆ R₊ t^m`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_tPow_mul_eq_mul_tPow (m : ℤ) {x : SkewLaurent S} (hx : x ∈ skewHalf S 1) :
    ∃ y ∈ skewHalf S 1, tPow S m * x = y * tPow S m :=
  ⟨tPow S m * x * tPow S (-m), conj_tPow_mem_skewHalf_one m hx, tPow_mul_eq_conj_mul m x⟩

/-- `R₊ t^m ⊆ t^m R₊`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_mul_tPow_eq_tPow_mul (m : ℤ) {x : SkewLaurent S} (hx : x ∈ skewHalf S 1) :
    ∃ y ∈ skewHalf S 1, x * tPow S m = tPow S m * y := by
  refine ⟨tPow S (-m) * x * tPow S (-(-m)), conj_tPow_mem_skewHalf_one (-m) hx, ?_⟩
  rw [neg_neg, ← mul_assoc, ← mul_assoc, tPow_mul_tPow_neg, one_mul]

end Normal

section Augmentation

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- If `x ∈ S[t;φ]` has constant term `0` then `t⁻¹ x ∈ S[t;φ]`.
(`yaoseq6.tex` `thm:skewyao`, Step 1, the augmentation `R[t₊] → R`;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem tPow_neg_one_mul_mem_of_coeff_one_eq_zero {x : SkewLaurent S} (hx : x ∈ skewHalf S 1)
    (h0 : SkewMonoidAlgebra.coeff x 1 = 0) : tPow S (-1) * x ∈ skewHalf S 1 := by
  have hx' := (mem_halfSupport S).mp (skewHalf_le_halfSupport S 1 hx)
  rw [skewHalf_one_eq_halfSupport, mem_halfSupport]
  intro g hg
  rw [tPow, SkewMonoidAlgebra.coeff_single_mul, one_mul]
  have hz : Multiplicative.toAdd ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ * g) =
      1 + Multiplicative.toAdd g := by
    rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, neg_neg]
  by_cases hlt : 1 + Multiplicative.toAdd g < 0
  · have hc : SkewMonoidAlgebra.coeff x ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ * g) = 0 :=
      hx' ((Multiplicative.ofAdd (-1 : ℤ))⁻¹ * g) (by rw [hz]; omega)
    rw [hc, smul_zero]
  · have he : (Multiplicative.ofAdd (-1 : ℤ))⁻¹ * g = 1 :=
      toAdd_eq_zero.mp (by rw [hz]; omega)
    rw [he, h0, smul_zero]

/-- **The augmentation ideal is `t R₊`**: an element of `S[t;φ]` with constant term `0` is `t y`
with `y ∈ S[t;φ]`, so `S[t;φ]/t S[t;φ] = S`.  (`yaoseq6.tex` `thm:skewyao`, Step 1;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_eq_tPow_one_mul_of_coeff_one_eq_zero {x : SkewLaurent S}
    (hx : x ∈ skewHalf S 1) (h0 : SkewMonoidAlgebra.coeff x 1 = 0) :
    ∃ y ∈ skewHalf S 1, x = tPow S 1 * y :=
  ⟨tPow S (-1) * x, tPow_neg_one_mul_mem_of_coeff_one_eq_zero hx h0,
    by rw [← mul_assoc, tPow_mul_tPow_neg, one_mul]⟩

/-- **The augmentation ideal is `R₊ t`**: an element of `S[t;φ]` with constant term `0` is `y t`
with `y ∈ S[t;φ]`.  (`yaoseq6.tex` `thm:skewyao`, Step 1; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem exists_eq_mul_tPow_one_of_coeff_one_eq_zero {x : SkewLaurent S}
    (hx : x ∈ skewHalf S 1) (h0 : SkewMonoidAlgebra.coeff x 1 = 0) :
    ∃ y ∈ skewHalf S 1, x = y * tPow S 1 := by
  obtain ⟨y, hy, rfl⟩ := exists_eq_tPow_one_mul_of_coeff_one_eq_zero hx h0
  exact exists_tPow_mul_eq_mul_tPow 1 hy

end Augmentation

end GroupApproximation.Full.LVOreLocK2
