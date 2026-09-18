import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraNorm
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraModuleComplete

/-!
# Completeness of `𝓛(H_J)`

Lane `TWWSch3d3-2C`, work order `WO-3d3-2C`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through the Busby picture of `Ext(S, J)` used in
Schafhauser's proof of the Tikuisis--White--Winter theorem.

The operator norm on `StdBdd J = 𝓛(H_J)` (`StdOperatorAlgebraNorm`) is complete (Lance, *Hilbert
C⋆-modules*, Ch. 1, the proof that `𝓛(E)` is a C⋆-algebra):

* `StdBdd.norm_star_eq`: `‖T⋆‖ = ‖T‖`;
* `StdBdd.exists_pointwise_limit`: a Cauchy sequence of operators converges uniformly on bounded
  sets, using completeness of `H_J` (`stdModule_cauchy_limit`);
* `StdBdd.instCompleteSpace`: the pointwise limits of `Tₙ` and `Tₙ⋆` are mutually adjoint and
  bounded, so they define an element of `StdBdd J`, and `Tₙ` converges to it in norm.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule Filter Topology

noncomputable section

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The adjoint is isometric (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Lance,
Ch. 1). -/
theorem StdBdd.norm_star_eq (U : StdBdd J) : ‖star U‖ = ‖U‖ :=
  Adjointable.opNorm_adjoint U.isBounded

/-- A Cauchy sequence of operators in the `ε`--`N` form (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.cauchy_bound (T : ℕ → StdBdd J) (hT : CauchySeq T) :
    ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖T m - T n‖ ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hT ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have h := hN m hm n hn
  rw [dist_eq_norm_sub] at h
  exact h.le

/-- **A Cauchy sequence of operators has a pointwise limit**, attained uniformly on bounded sets
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Lance, Ch. 1). -/
theorem StdBdd.exists_pointwise_limit (T : ℕ → StdBdd J)
    (hT : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖T m - T n‖ ≤ ε) :
    ∃ S : (standardModule ℕ J).carrier → (standardModule ℕ J).carrier, ∀ ε > 0, ∃ N, ∀ n ≥ N,
      ∀ x, (standardModule ℕ J).norm ((T n).1.toFun x - S x)
        ≤ ε * (standardModule ℕ J).norm x := by
  have hpt : ∀ x : (standardModule ℕ J).carrier, ∃ s : (standardModule ℕ J).carrier,
      ∀ ε > 0, ∃ N, ∀ n ≥ N, (standardModule ℕ J).norm ((T n).1.toFun x - s) ≤ ε := by
    intro x
    refine stdModule_cauchy_limit (fun n => (T n).1.toFun x) fun ε hε => ?_
    have hx : 0 < (standardModule ℕ J).norm x + 1 := by
      linarith [(standardModule ℕ J).norm_nonneg x]
    obtain ⟨N, hN⟩ := hT (ε / ((standardModule ℕ J).norm x + 1)) (div_pos hε hx)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 : (standardModule ℕ J).norm ((T m).1.toFun x - (T n).1.toFun x)
        ≤ ‖T m - T n‖ * (standardModule ℕ J).norm x :=
      StdBdd.norm_apply_le (T m - T n) x
    have h2 := mul_le_mul_of_nonneg_right (hN m hm n hn) ((standardModule ℕ J).norm_nonneg x)
    have h3 : ε / ((standardModule ℕ J).norm x + 1) * (standardModule ℕ J).norm x ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hx]
      nlinarith [(standardModule ℕ J).norm_nonneg x]
    exact h1.trans (h2.trans h3)
  choose S hS using hpt
  refine ⟨S, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hT ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have key : ∀ δ > 0, (standardModule ℕ J).norm ((T n).1.toFun x - S x)
      - ε * (standardModule ℕ J).norm x ≤ δ * 1 := by
    intro δ hδ
    obtain ⟨M, hM⟩ := hS x δ hδ
    have hm1 : max M N ≥ M := le_max_left M N
    have hm2 : max M N ≥ N := le_max_right M N
    have htri := (standardModule ℕ J).norm_add_le
      ((T n).1.toFun x - (T (max M N)).1.toFun x) ((T (max M N)).1.toFun x - S x)
    rw [sub_add_sub_cancel] at htri
    have h1 : (standardModule ℕ J).norm ((T n).1.toFun x - (T (max M N)).1.toFun x)
        ≤ ‖T n - T (max M N)‖ * (standardModule ℕ J).norm x :=
      StdBdd.norm_apply_le (T n - T (max M N)) x
    have h2 := mul_le_mul_of_nonneg_right (hN n hn (max M N) hm2)
      ((standardModule ℕ J).norm_nonneg x)
    have h3 := hM (max M N) hm1
    linarith
  have h0 := stdAux_le_zero zero_le_one key
  linarith

/-- **`𝓛(H_J)` is complete** (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Lance,
Ch. 1): the pointwise limit of a Cauchy sequence `Tₙ` has the pointwise limit of `Tₙ⋆` as an
adjoint, is bounded, and is the norm limit of `Tₙ`. -/
instance StdBdd.instCompleteSpace : CompleteSpace (StdBdd J) := by
  refine EMetric.complete_of_cauchySeq_tendsto fun T hT => ?_
  have hTb := StdBdd.cauchy_bound T hT
  have hTs : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖star (T m) - star (T n)‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hTb ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [← star_sub, StdBdd.norm_star_eq]
    exact hN m hm n hn
  obtain ⟨S, hS⟩ := StdBdd.exists_pointwise_limit T hTb
  obtain ⟨S', hS'⟩ := StdBdd.exists_pointwise_limit (fun n => star (T n)) hTs
  have hinner : ∀ x y, (standardModule ℕ J).inner (S x) y
      = (standardModule ℕ J).inner x (S' y) := by
    intro x y
    have hx := (standardModule ℕ J).norm_nonneg x
    have hy := (standardModule ℕ J).norm_nonneg y
    have hbound : ∀ ε > 0,
        ‖(standardModule ℕ J).inner (S x) y - (standardModule ℕ J).inner x (S' y)‖
          ≤ ε * (2 * ((standardModule ℕ J).norm x * (standardModule ℕ J).norm y)) := by
      intro ε hε
      obtain ⟨N1, hN1⟩ := hS ε hε
      obtain ⟨N2, hN2⟩ := hS' ε hε
      have h1 := hN1 (max N1 N2) (le_max_left N1 N2) x
      have h2 : (standardModule ℕ J).norm ((T (max N1 N2)).1.adj y - S' y)
          ≤ ε * (standardModule ℕ J).norm y :=
        hN2 (max N1 N2) (le_max_right N1 N2) y
      have hrel := (T (max N1 N2)).1.inner_adj x y
      have hdec : (standardModule ℕ J).inner (S x) y - (standardModule ℕ J).inner x (S' y)
          = (standardModule ℕ J).inner x ((T (max N1 N2)).1.adj y - S' y)
            - (standardModule ℕ J).inner ((T (max N1 N2)).1.toFun x - S x) y := by
        rw [CStarModule.inner_sub_right, CStarModule.inner_sub_left, ← hrel]
        abel
      rw [hdec]
      have h3 := norm_sub_le ((standardModule ℕ J).inner x ((T (max N1 N2)).1.adj y - S' y))
        ((standardModule ℕ J).inner ((T (max N1 N2)).1.toFun x - S x) y)
      have h4 := (standardModule ℕ J).norm_inner_le x ((T (max N1 N2)).1.adj y - S' y)
      have h5 := (standardModule ℕ J).norm_inner_le ((T (max N1 N2)).1.toFun x - S x) y
      have h6 := mul_le_mul_of_nonneg_left h2 hx
      have h7 := mul_le_mul_of_nonneg_right h1 hy
      linarith
    have h0 := stdAux_le_zero (mul_nonneg zero_le_two (mul_nonneg hx hy)) hbound
    have hz : ‖(standardModule ℕ J).inner (S x) y - (standardModule ℕ J).inner x (S' y)‖ = 0 :=
      le_antisymm h0 (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 hz)
  obtain ⟨N1, hN1⟩ := hS 1 one_pos
  have hbd : ∀ x, (standardModule ℕ J).norm (S x)
      ≤ (‖T N1‖ + 1) * (standardModule ℕ J).norm x := by
    intro x
    have h1 := hN1 N1 le_rfl x
    have h2 := StdBdd.norm_apply_le (T N1) x
    have h3 := (standardModule ℕ J).norm_add_le (S x - (T N1).1.toFun x) ((T N1).1.toFun x)
    rw [sub_add_cancel, ← neg_sub, (standardModule ℕ J).norm_neg] at h3
    linarith
  obtain ⟨L, hL⟩ : ∃ L : StdBdd J, ∀ x, L.1.toFun x = S x :=
    ⟨⟨⟨S, S', hinner⟩, mem_boundedAdj.mpr
      ⟨‖T N1‖ + 1, by linarith [StdBdd.norm_nonneg' (T N1)], hbd⟩⟩, fun _ => rfl⟩
  refine ⟨L, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hS (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hb : (T n - L).1.IsBoundedBy (ε / 2) := by
    intro x
    have h := hN n hn x
    rw [← hL x] at h
    exact h
  rw [dist_eq_norm_sub]
  have h1 : ‖T n - L‖ ≤ ε / 2 :=
    (StdBdd.norm_def _).trans_le (Adjointable.opNorm_le_of_bound (half_pos hε).le hb)
  linarith

end

end GroupApproximation.Full.TWWSchafhauser
