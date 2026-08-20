import GroupApproximation.Analysis.CStarCompactOperators

/-!
# `𝓚(B_B) = B`, and `B ⊆ M(B)` isometrically

The two classical identifications that make the multiplier algebra of
`Analysis.CStarAdjointable` the right object: on the module `B` over itself,
the **compact** operators are exactly the left multiplications, and the
embedding `b ↦ (x ↦ bx)` of `B` into `𝓛(B_B) = M(B)` is **isometric**.

Together they say `M(B) = 𝓛(𝓚(B))` in the case `E = B`, which is the case the
Winter--Zacharias factorization is stated over.

## What is proved

* `norm_le_of_forall_mul_le` --- if `‖bx‖ ≤ K‖x‖` for all `x` then `‖b‖ ≤ K`.
  The witness is `x = b⋆`, where the C⋆-identity turns the estimate into
  `‖b‖² ≤ K‖b‖`.  Without the C⋆-identity this is false --- a Banach algebra
  can have elements of large norm acting as small multipliers --- so this is
  the one place the left-regular representation being isometric is genuinely a
  C⋆-fact;
* `opNorm_ofElem : ‖ofElem b‖ = ‖b‖`;
* `IsFiniteRank.exists_ofElem` --- a finite-rank operator on `B` is left
  multiplication by `∑ xᵢyᵢ⋆`, because `θ_{x,y}z = x(y⋆z) = (xy⋆)z`;
* `isCompactOp_ofElem` --- **every** left multiplication is compact.  This is
  where an approximate unit is needed: `ofElem (be) = θ_{b,e⋆}` is rank one,
  and `be → b` along the approximate unit of `B`.  For unital `B` the point is
  trivial (`ofElem b = θ_{b,1}`); the content is the non-unital case, and it
  is the reason `𝓚(B_B)` is all of `B` rather than a proper ideal;
* `isCompactOp_iff_exists_ofElem` --- the identification, in both directions.
  The hard direction is a completeness argument: the approximants are `ofElem
  cₙ`, the isometry makes `(cₙ)` Cauchy in `B`, and its limit represents the
  operator.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero Filter Topology

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

/-! ## The norm of a multiplier -/

/-- **A bound on left multiplication is a bound on the element.**  Test at
`x = b⋆` and use the C⋆-identity. -/
theorem norm_le_of_forall_mul_le {b : B} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x : B, ‖b * x‖ ≤ K * ‖x‖) : ‖b‖ ≤ K := by
  rcases eq_or_ne b 0 with rfl | hb
  · simpa using hK
  · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have h1 : ‖b * star b‖ ≤ K * ‖star b‖ := h (star b)
    rw [CStarRing.norm_self_mul_star, norm_star] at h1
    exact le_of_mul_le_mul_right h1 hbpos

namespace Adjointable

theorem isBoundedBy_ofElem (b : B) : (ofElem b).IsBoundedBy ‖b‖ := by
  intro x
  show (selfModule B).norm (b * x) ≤ ‖b‖ * (selfModule B).norm x
  simp only [selfModule_norm]
  exact norm_mul_le b x

theorem isBounded_ofElem (b : B) : (ofElem b).IsBounded :=
  ⟨‖b‖, norm_nonneg b, isBoundedBy_ofElem b⟩

/-- **`B` sits isometrically in `M(B)`.** -/
theorem opNorm_ofElem (b : B) : (ofElem b).opNorm = ‖b‖ := by
  refine le_antisymm (opNorm_le_of_bound (norm_nonneg b) (isBoundedBy_ofElem b))
    ?_
  refine norm_le_of_forall_mul_le (opNorm_nonneg _) fun x => ?_
  have h := norm_apply_le_opNorm (isBounded_ofElem b) x
  simpa only [selfModule_norm] using h

/-! ## Finite-rank operators on `B` -/

/-- A finite-rank operator on `B` is left multiplication by `∑ xᵢyᵢ⋆`. -/
theorem IsFiniteRank.exists_ofElem {T : Multiplier B} (h : T.IsFiniteRank) :
    ∃ b : B, ∀ x : B, T.toFun x = b * x := by
  obtain ⟨ι, hι, x, y, hT⟩ := h
  refine ⟨∑ i, x i * star (y i), fun z => ?_⟩
  rw [hT z, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  show x i * (star (y i) * z) = x i * star (y i) * z
  rw [mul_assoc]

/-! ## Every left multiplication is compact -/

/-- **Left multiplication by any element of `B` is a compact operator.**

`ofElem (be) = θ_{b,e⋆}` is rank one, and `be → b` along the approximate unit
of `B`; for non-unital `B` this is the whole content. -/
theorem isCompactOp_ofElem (b : B) : (ofElem b).IsCompactOp := by
  refine ⟨isBounded_ofElem b, ?_⟩
  intro ε hε
  have htend : Tendsto (b * ·) (CStarAlgebra.approximateUnit B) (𝓝 b) :=
    (CStarAlgebra.increasingApproximateUnit B).tendsto_mul_left b
  have hev : ∀ᶠ e in CStarAlgebra.approximateUnit B, ‖b * e - b‖ < ε := by
    have h := Metric.tendsto_nhds.mp htend ε hε
    simpa only [dist_eq_norm] using h
  obtain ⟨e, he⟩ := hev.exists
  refine ⟨rankOne b (star e), isFiniteRank_rankOne _ _, ?_⟩
  intro x
  show (selfModule B).norm (b * x - b * (star (star e) * x))
      ≤ ε * (selfModule B).norm x
  simp only [selfModule_norm]
  rw [star_star]
  have hfac : b * x - b * (e * x) = (b - b * e) * x := by
    rw [sub_mul, mul_assoc]
  rw [hfac]
  refine le_trans (norm_mul_le _ _) ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
  rw [norm_sub_rev]
  exact le_of_lt he

/-! ## The identification -/

/-- A compact operator on `B` is left multiplication by an element of `B`.

The approximants are `ofElem cₙ`; the isometry `opNorm_ofElem` makes `(cₙ)`
Cauchy, and `B` is complete. -/
theorem IsCompactOp.exists_ofElem {T : Multiplier B} (hT : T.IsCompactOp) :
    ∃ b : B, ∀ x : B, T.toFun x = b * x := by
  choose S hSfin hSb using fun n : ℕ => hT.2 (1 / (n + 1 : ℝ)) (by positivity)
  choose c hc using fun n : ℕ => (hSfin n).exists_ofElem
  have hkey : ∀ (n : ℕ) (x : B),
      ‖T.toFun x - c n * x‖ ≤ (1 / (n + 1 : ℝ)) * ‖x‖ := by
    intro n x
    have h := hSb n x
    simp only [selfModule_norm, sub_toFun] at h
    rw [← hc n x]
    exact h
  have hCauchyBound : ∀ n m : ℕ,
      ‖c n - c m‖ ≤ 1 / (n + 1 : ℝ) + 1 / (m + 1 : ℝ) := by
    intro n m
    refine norm_le_of_forall_mul_le (by positivity) fun x => ?_
    have hfac : (c n - c m) * x
        = (T.toFun x - c m * x) - (T.toFun x - c n * x) := by
      rw [sub_mul]
      abel
    rw [hfac]
    calc ‖(T.toFun x - c m * x) - (T.toFun x - c n * x)‖
        ≤ ‖T.toFun x - c m * x‖ + ‖T.toFun x - c n * x‖ := norm_sub_le _ _
      _ ≤ (1 / (m + 1 : ℝ)) * ‖x‖ + (1 / (n + 1 : ℝ)) * ‖x‖ :=
          add_le_add (hkey m x) (hkey n x)
      _ = (1 / (n + 1 : ℝ) + 1 / (m + 1 : ℝ)) * ‖x‖ := by ring
  have hcau : CauchySeq c := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 / (N + 1 : ℝ)) ?_ ?_
    · intro n m N hn hm
      have hNn : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact_mod_cast Nat.succ_le_succ hn
      have hNm : (1 : ℝ) / (m + 1) ≤ 1 / (N + 1) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        exact_mod_cast Nat.succ_le_succ hm
      rw [dist_eq_norm]
      refine le_trans (hCauchyBound n m) ?_
      have h2 : (2 : ℝ) / (N + 1) = 1 / (N + 1) + 1 / (N + 1) := by ring
      rw [h2]
      exact add_le_add hNn hNm
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
      simpa only [mul_zero, mul_one_div] using h
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨b, fun x => ?_⟩
  have hbound : ∀ n : ℕ, ‖T.toFun x - b * x‖
      ≤ (1 / (n + 1 : ℝ)) * ‖x‖ + ‖c n - b‖ * ‖x‖ := by
    intro n
    have hsplit : T.toFun x - b * x
        = (T.toFun x - c n * x) + (c n - b) * x := by
      rw [sub_mul]
      abel
    rw [hsplit]
    exact le_trans (norm_add_le _ _)
      (add_le_add (hkey n x) (norm_mul_le _ _))
  have htend0 : Tendsto
      (fun n : ℕ => (1 / (n + 1 : ℝ)) * ‖x‖ + ‖c n - b‖ * ‖x‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) * ‖x‖) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖x‖
    have hc0 : Tendsto (fun n : ℕ => ‖c n - b‖) atTop (𝓝 0) := by
      simpa using (hb.sub tendsto_const_nhds).norm
    have h2 : Tendsto (fun n : ℕ => ‖c n - b‖ * ‖x‖) atTop (𝓝 0) := by
      simpa using hc0.mul_const ‖x‖
    simpa using h1.add h2
  have hle : ‖T.toFun x - b * x‖ ≤ 0 := ge_of_tendsto' htend0 hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hle (norm_nonneg _)))

/-- **`𝓚(B_B) = B`**: the compact operators on `B` as a module over itself are
exactly the left multiplications. -/
theorem isCompactOp_iff_exists_ofElem {T : Multiplier B} :
    T.IsCompactOp ↔ ∃ b : B, ∀ x : B, T.toFun x = b * x := by
  refine ⟨fun h => h.exists_ofElem, ?_⟩
  rintro ⟨b, hb⟩
  exact IsCompactOp.congr (fun x => (hb x).symm) (isCompactOp_ofElem b)

end Adjointable

end HilbertModule
end GroupApproximation
