import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Cohn

/-!
# The corner shift of the Cohn algebra (lane LVCohnColimit, WO-LVCohnK2-4)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  Source:
Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*, Münster J. Math. 2 (2009),
`thm:skewyao`, Step 3 (`yaoseq6.tex` l.640-688).  There the Cohn algebra `C = C_2(𝔽₂)` is a
corner skew Laurent ring `C_0[t₊, t₋; φ]` with `t₋ t₊ = 1`, `φ(a) = t₊ a t₋`, and the
endomorphism `η(a) = t₊ a t₋` acts as the identity on `K`-theory.  For `C_2(𝔽₂)`,
`t₊ = x₀` and `t₋ = y₀` (`y₀ x₀ = 1`).

This file contains the ring-theoretic part:
* `cornerShift u v h`: for `v * u = 1`, the non-unital ring endomorphism `a ↦ u a v`;
* `cohnShift`: the case `u = x₀`, `v = y₀` of the Cohn algebra (target of WO-LVCohnK2-4);
* `cornerUnital u v h`: the unital extension `(c, ε) ↦ (u c v + ε (1 - u v), ε)` on `R × K`,
  which is a unital ring endomorphism because `v (1 - u v) = 0 = (1 - u v) u`; it restricts to
  `cornerShift` on `R × 0` and composes as `θ_{u,v} ∘ θ_{u',v'} = θ_{u u', v' v}`;
* `cohnTheta m`: the unital shift `θ_{x₀^m, y₀^m}` of `C_2(𝔽₂) × 𝔽₂`.
-/

namespace GroupApproximation.Full.LVCohnColimit

noncomputable section

section Corner

variable {R : Type*} [Ring R]

/-- For `v * u = 1`, the non-unital ring endomorphism `a ↦ u a v`.
(`yaoseq6.tex` `thm:skewyao`, Step 3, `η(x) = t₊ x t₋`; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
def cornerShift (u v : R) (h : v * u = 1) : R →ₙ+* R where
  toFun a := u * a * v
  map_mul' a b := by
    show u * (a * b) * v = u * a * v * (u * b * v)
    simp only [mul_assoc]
    rw [← mul_assoc v u (b * v), h, one_mul]
  map_zero' := by
    show u * 0 * v = 0
    rw [mul_zero, zero_mul]
  map_add' a b := by
    show u * (a + b) * v = u * a * v + u * b * v
    rw [mul_add, add_mul]

/-- `cornerShift u v h a = u * a * v`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerShift_apply (u v : R) (h : v * u = 1) (a : R) :
    cornerShift u v h a = u * a * v :=
  rfl

/-- Powers of a one-sided inverse pair: `v * u = 1` gives `v ^ m * u ^ m = 1`.
(`yaoseq6.tex` `thm:skewyao`, Step 3, `t₋^m t₊^m = 1`; `simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem pow_mul_pow_eq_one_of_mul_eq_one {u v : R} (h : v * u = 1) :
    ∀ m : ℕ, v ^ m * u ^ m = 1
  | 0 => by rw [pow_zero, pow_zero, one_mul]
  | m + 1 => by
    rw [pow_succ v m, pow_succ' u m, mul_assoc (v ^ m) v (u * u ^ m),
      ← mul_assoc v u (u ^ m), h, one_mul, pow_mul_pow_eq_one_of_mul_eq_one h m]

/-- `v (1 - u v) = 0` for `v * u = 1`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem mul_one_sub_mul_eq_zero {u v : R} (h : v * u = 1) : v * (1 - u * v) = 0 := by
  rw [mul_sub, mul_one, ← mul_assoc v u v, h, one_mul, sub_self]

/-- `(1 - u v) u = 0` for `v * u = 1`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem one_sub_mul_mul_eq_zero {u v : R} (h : v * u = 1) : (1 - u * v) * u = 0 := by
  rw [sub_mul, one_mul, mul_assoc u v u, h, mul_one, sub_self]

/-- `1 - u v` is idempotent for `v * u = 1`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem one_sub_mul_idem {u v : R} (h : v * u = 1) :
    (1 - u * v) * (1 - u * v) = 1 - u * v := by
  rw [mul_sub (1 - u * v) 1 (u * v), mul_one, ← mul_assoc (1 - u * v) u v,
    one_sub_mul_mul_eq_zero h, zero_mul, sub_zero]

variable {K : Type*} [CommRing K] [Algebra K R]

/-- The unital shift `θ_{u,v} : R × K → R × K`, `(c, ε) ↦ (u c v + ε (1 - u v), ε)`, for
`v * u = 1`.  It extends `cornerShift u v h` (on `R × 0`) to a unital ring endomorphism of the
unitization-type ring `R × K`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cornerUnital (u v : R) (h : v * u = 1) : R × K →+* R × K where
  toFun c := (u * c.1 * v + algebraMap K R c.2 * (1 - u * v), c.2)
  map_one' := by
    refine Prod.ext ?_ rfl
    show u * 1 * v + algebraMap K R 1 * (1 - u * v) = 1
    rw [mul_one, map_one, one_mul, add_sub_cancel]
  map_mul' c d := by
    obtain ⟨a, s⟩ := c
    obtain ⟨b, t⟩ := d
    refine Prod.ext ?_ rfl
    show u * (a * b) * v + algebraMap K R (s * t) * (1 - u * v) =
      (u * a * v + algebraMap K R s * (1 - u * v)) *
        (u * b * v + algebraMap K R t * (1 - u * v))
    have h1 : u * a * v * (u * b * v) = u * (a * b) * v := by
      simp only [mul_assoc]
      rw [← mul_assoc v u (b * v), h, one_mul]
    have hvt : v * (algebraMap K R t * (1 - u * v)) = 0 := by
      rw [← mul_assoc v (algebraMap K R t) (1 - u * v), ← Algebra.commutes t v,
        mul_assoc (algebraMap K R t) v (1 - u * v), mul_one_sub_mul_eq_zero h, mul_zero]
    have h2 : u * a * v * (algebraMap K R t * (1 - u * v)) = 0 := by
      rw [mul_assoc (u * a) v (algebraMap K R t * (1 - u * v)), hvt, mul_zero]
    have h3 : algebraMap K R s * (1 - u * v) * (u * b * v) = 0 := by
      rw [mul_assoc (algebraMap K R s) (1 - u * v) (u * b * v),
        ← mul_assoc (1 - u * v) (u * b) v, ← mul_assoc (1 - u * v) u b,
        one_sub_mul_mul_eq_zero h, zero_mul, zero_mul, mul_zero]
    have h4 : algebraMap K R s * (1 - u * v) * (algebraMap K R t * (1 - u * v)) =
        algebraMap K R (s * t) * (1 - u * v) := by
      rw [map_mul, mul_assoc (algebraMap K R s) (1 - u * v) (algebraMap K R t * (1 - u * v)),
        ← mul_assoc (1 - u * v) (algebraMap K R t) (1 - u * v),
        ← Algebra.commutes t (1 - u * v),
        mul_assoc (algebraMap K R t) (1 - u * v) (1 - u * v), one_sub_mul_idem h,
        ← mul_assoc (algebraMap K R s) (algebraMap K R t) (1 - u * v)]
    rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add]
  map_zero' := by
    refine Prod.ext ?_ rfl
    show u * 0 * v + algebraMap K R 0 * (1 - u * v) = 0
    rw [mul_zero, zero_mul, map_zero, zero_mul, add_zero]
  map_add' c d := by
    obtain ⟨a, s⟩ := c
    obtain ⟨b, t⟩ := d
    refine Prod.ext ?_ rfl
    show u * (a + b) * v + algebraMap K R (s + t) * (1 - u * v) =
      (u * a * v + algebraMap K R s * (1 - u * v)) +
        (u * b * v + algebraMap K R t * (1 - u * v))
    rw [mul_add, add_mul, map_add, add_mul]
    exact add_add_add_comm _ _ _ _

/-- The first coordinate of `θ_{u,v}`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerUnital_fst (u v : R) (h : v * u = 1) (c : R × K) :
    (cornerUnital u v h c).1 = u * c.1 * v + algebraMap K R c.2 * (1 - u * v) :=
  rfl

/-- The second coordinate of `θ_{u,v}`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerUnital_snd (u v : R) (h : v * u = 1) (c : R × K) :
    (cornerUnital u v h c).2 = c.2 :=
  rfl

/-- On `R × 0` the unital shift is the corner shift.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerUnital_inl (u v : R) (h : v * u = 1) (a : R) :
    cornerUnital (K := K) u v h (a, 0) = (cornerShift u v h a, 0) := by
  refine Prod.ext ?_ rfl
  show u * a * v + algebraMap K R 0 * (1 - u * v) = u * a * v
  rw [map_zero, zero_mul, add_zero]

/-- The product of two one-sided inverse pairs is one.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem mul_mul_mul_eq_one {u v u' v' : R} (h : v * u = 1) (h' : v' * u' = 1) :
    v' * v * (u * u') = 1 := by
  rw [mul_assoc v' v (u * u'), ← mul_assoc v u u', h, one_mul, h']

/-- Composition law `θ_{u,v} ∘ θ_{u',v'} = θ_{u u', v' v}`.  (`yaoseq6.tex` `thm:skewyao`,
Step 3, the colimit maps `φ_n`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerUnital_comp {u v u' v' : R} (h : v * u = 1) (h' : v' * u' = 1) :
    (cornerUnital (K := K) u v h).comp (cornerUnital u' v' h') =
      cornerUnital (u * u') (v' * v) (mul_mul_mul_eq_one h h') := by
  refine RingHom.ext ?_
  rintro ⟨c, ε⟩
  refine Prod.ext ?_ rfl
  show u * (u' * c * v' + algebraMap K R ε * (1 - u' * v')) * v +
      algebraMap K R ε * (1 - u * v) =
    u * u' * c * (v' * v) + algebraMap K R ε * (1 - u * u' * (v' * v))
  have e1 : u * (u' * c * v') * v = u * u' * c * (v' * v) := by
    simp only [mul_assoc]
  have e2 : u * v - u * (u' * v') * v + (1 - u * v) = 1 - u * u' * (v' * v) := by
    simp only [mul_assoc]
    abel
  rw [mul_add, add_mul, Algebra.left_comm u ε (1 - u' * v'),
    mul_assoc (algebraMap K R ε) (u * (1 - u' * v')) v, mul_sub u 1 (u' * v'), mul_one u,
    sub_mul u (u * (u' * v')) v, add_assoc, ← mul_add (algebraMap K R ε), e1, e2]

/-- `θ_{u,v}` depends only on `u` and `v`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cornerUnital_congr {u v u₁ v₁ : R} (h : v * u = 1) (h₁ : v₁ * u₁ = 1)
    (hu : u = u₁) (hv : v = v₁) : cornerUnital (K := K) u v h = cornerUnital u₁ v₁ h₁ := by
  subst hu
  subst hv
  rfl

end Corner

section Cohn

open LVCohnRelK1

/-- **The Cohn shift** `η(a) = x₀ a y₀` on `C_2(𝔽₂)`, a non-unital ring endomorphism since
`y₀ x₀ = 1`.  (Target of WO-LVCohnK2-4; `yaoseq6.tex` `thm:skewyao`, Step 3,
`η(x) = t₊ x t₋`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cohnShift : CohnTwoF2 →ₙ+* CohnTwoF2 :=
  cornerShift (cx false) (cy false) y0_x0

/-- `cohnShift a = x₀ a y₀`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnShift_apply (a : CohnTwoF2) : cohnShift a = cx false * a * cy false :=
  rfl

/-- `y₀^m x₀^m = 1` in `C_2(𝔽₂)`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cy_pow_mul_cx_pow (m : ℕ) : cy false ^ m * cx false ^ m = 1 :=
  pow_mul_pow_eq_one_of_mul_eq_one y0_x0 m

/-- The unital shift `θ_m = θ_{x₀^m, y₀^m}` of `C_2(𝔽₂) × 𝔽₂`,
`(c, ε) ↦ (x₀^m c y₀^m + ε (1 - x₀^m y₀^m), ε)`.  (`yaoseq6.tex` `thm:skewyao`, Step 3,
the maps `φ_n`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def cohnTheta (m : ℕ) : CohnTwoF2 × ZMod 2 →+* CohnTwoF2 × ZMod 2 :=
  cornerUnital (cx false ^ m) (cy false ^ m) (cy_pow_mul_cx_pow m)

/-- `θ_1 ∘ θ_m = θ_{m+1}`.  (`yaoseq6.tex` `thm:skewyao`, Step 3;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnTheta_one_comp (m : ℕ) : (cohnTheta 1).comp (cohnTheta m) = cohnTheta (m + 1) :=
  (cornerUnital_comp (K := ZMod 2) (cy_pow_mul_cx_pow 1) (cy_pow_mul_cx_pow m)).trans
    (cornerUnital_congr _ (cy_pow_mul_cx_pow (m + 1)) (by rw [pow_one, pow_succ'])
      (by rw [pow_one, pow_succ]))

/-- On `C_2(𝔽₂) × 0` the unital shift `θ_m` is `a ↦ x₀^m a y₀^m`.  (`yaoseq6.tex`
`thm:skewyao`, Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem cohnTheta_inl (m : ℕ) (a : CohnTwoF2) :
    cohnTheta m (a, 0) = (cx false ^ m * a * cy false ^ m, 0) :=
  cornerUnital_inl (cx false ^ m) (cy false ^ m) (cy_pow_mul_cx_pow m) a

end Cohn

end

end GroupApproximation.Full.LVCohnColimit
