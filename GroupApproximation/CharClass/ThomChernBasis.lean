import GroupApproximation.CharClass.ChernClasses
import GroupApproximation.CharClass.ThomClassChain

/-!
# The Chern relation in the Leray–Hirsch basis

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypotheses 6 and 7).

`CharClass/ThomClassChain.lean` builds the Thom class of the pair
`(P(E⊕1), P(E⊕1) ∖ Z)` from two `Module.Basis` terms and two equations describing
the restriction:

```text
hcast : ρ (b i.castSucc) = b' i        (i < r)
hlast : ρ (b (Fin.last r)) = -∑ i, c i • b' i
```

`cc-projective`'s `CharClass/ChernClasses.lean` supplies the bases: a
`LerayHirschData` presents `TotalH P` as a `PowerBasis (TotalH X) (TotalH P)`,
whose `basis` is `1, ξ, …, ξ^{r-1}`, and defines the mod-2 Chern classes as the
coefficients of its monic relation.  This file supplies the second equation, in
the form `hlast` wants it: the Chern relation solved for the top power of the
generator, written in the basis.

That is pure algebra about a `PowerBasis`, with no topology in it at all — the
`hcast` half, that the tautological class of `P(E⊕1)` restricts to the
tautological class of `P(E)`, is `cc-projective`'s and is not here.

`totalMap_comp` is the functoriality of `TotalH.map` that makes the restriction a
map of algebras over the base; it is stated here under a lane-local name rather
than added to `ChernTotalRing.lean`, which is `cc-projective`'s file.

## Main declarations

* `ThomChern.genPow_dim_eq_neg_sum` — `ξ^r = -∑_{i<r} γ_{r-i} ξ^i`, over `Finset.range`.
* `ThomChern.genPow_dim_eq_neg_finSum` — the same over `Fin r`.
* `ThomChern.genPow_dim_eq_neg_basisSum` — the same in the `PowerBasis` basis, which is
  the shape `ThomClassChain`'s `hlast` takes.
* `ThomChern.totalMap_comp`, `ThomChern.totalMap_id` — functoriality of `TotalH.map`.
-/

open CategoryTheory Polynomial

namespace GroupApproximation.CharClass

namespace ThomChern

noncomputable section

/-! ## 1. The Chern relation, solved for the top power -/

variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B]

/-- **The Chern relation, solved for the top power of the generator.**  From
`ξ^r + γ₁ ξ^{r-1} + ⋯ + γ_r = 0`, reindexed so that the coefficient of `ξ^i` is
`γ_{r-i}`. -/
theorem genPow_dim_eq_neg_sum [Nontrivial A] (pb : PowerBasis A B) :
    pb.gen ^ pb.dim
      = -∑ i ∈ Finset.range pb.dim, chernClass pb (pb.dim - i) • pb.gen ^ i := by
  have h : (aeval pb.gen) (chernPoly pb) = 0 := aeval_gen_chernPoly pb
  rw [chernPoly_eq_sum pb, map_sum] at h
  have h0 : ∑ k ∈ Finset.range (pb.dim + 1),
      chernClass pb k • pb.gen ^ (pb.dim - k) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl (fun k _ => by
      rw [map_mul, aeval_C, map_pow, aeval_X, ← Algebra.smul_def])
  rw [Finset.sum_range_succ', chernClass_zero, one_smul, Nat.sub_zero] at h0
  have h1 : pb.gen ^ pb.dim
      + ∑ k ∈ Finset.range pb.dim, chernClass pb (k + 1) • pb.gen ^ (pb.dim - (k + 1)) = 0 := by
    rw [add_comm]
    exact h0
  rw [eq_neg_of_add_eq_zero_left h1]
  congr 1
  rw [← Finset.sum_range_reflect (fun i => chernClass pb (pb.dim - i) • pb.gen ^ i) pb.dim]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < pb.dim := Finset.mem_range.mp hj
  have hexp : pb.dim - 1 - j = pb.dim - (j + 1) := by omega
  have hidx : pb.dim - (pb.dim - (j + 1)) = j + 1 := by omega
  simp only [hexp, hidx]

/-- The Chern relation over `Fin r`. -/
theorem genPow_dim_eq_neg_finSum [Nontrivial A] (pb : PowerBasis A B) :
    pb.gen ^ pb.dim
      = -∑ i : Fin pb.dim, chernClass pb (pb.dim - (i : ℕ)) • pb.gen ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => chernClass pb (pb.dim - i) • pb.gen ^ i) pb.dim]
  exact genPow_dim_eq_neg_sum pb

/-- **The Chern relation in the Leray–Hirsch basis.**  This is the shape
`ThomClassChain`'s `hlast` takes, with `c i = γ_{r-i}`. -/
theorem genPow_dim_eq_neg_basisSum [Nontrivial A] (pb : PowerBasis A B) :
    pb.gen ^ pb.dim
      = -∑ i : Fin pb.dim, chernClass pb (pb.dim - (i : ℕ)) • pb.basis i := by
  rw [genPow_dim_eq_neg_finSum pb]
  simp only [PowerBasis.coe_basis]

/-! ## 2. Functoriality of the total pullback -/

/-- `TotalH.map` is contravariantly functorial.  Stated under a lane-local name
because `ChernTotalRing.lean` belongs to `cc-projective`. -/
theorem totalMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : TotalH Z) :
    TotalH.map f (TotalH.map g a) = TotalH.map (f ≫ g) a := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      show TotalH.map f (TotalH.map g (TotalH.of Z n a)) = TotalH.map (f ≫ g) (TotalH.of Z n a)
      rw [TotalH.map_of, TotalH.map_of, TotalH.map_of, pull_comp]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The identity pulls back to the identity. -/
theorem totalMap_id {X : TopCat.{0}} (a : TotalH X) : TotalH.map (𝟙 X) a = a := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      show TotalH.map (𝟙 X) (TotalH.of X n a) = TotalH.of X n a
      rw [TotalH.map_of, pull_id]
  | add x y hx hy => rw [map_add, hx, hy]

end

end ThomChern

end GroupApproximation.CharClass
