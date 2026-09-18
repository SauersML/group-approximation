import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.YaoReduction

/-!
# Yao's factorization is equivalent to stable `K₂ = 0` (lane LVYaoCore)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; work order
WO-LVSkewLaurentK2-3a-1.  Ara–Brustenga–Cortiñas (2009) `thm:skewyao`, Step 1
(`yaoseq6.tex` l.574-640; Yao 1995, Thm 2.1).

`YaoReduction.lean` proves `StableK2Trivial (S[t,t⁻¹;φ])` from `K1Statement S`,
`HalfK2Statement S` and `YaoFactorization S`.  This file proves the converse direction, so that
under the two sibling inputs the Mayer–Vietoris factorization is *equivalent* to the endpoint:

* `yaoFactorization_of_stableK2Trivial`: stable `K₂(S[t,t⁻¹;φ]) = 0` gives the factorization
  (take `a = b = 1`, `g = 1` after padding);
* `yaoFactorization_iff_stableK2Trivial`: the equivalence.

Hence the Yao core is exactly as hard as the endpoint: it is the Steinberg-level form of Quillen
localization for the projective line over `S` (Yao 1995), not a reduction of it.
-/

namespace GroupApproximation.Full.LVSkewLaurentK2

open SteinbergGroup

section Equivalence

variable {S : Type*} [Ring S] [MulSemiringAction (Multiplicative ℤ) S]

/-- **Converse of Yao's reduction.**  If `S[t,t⁻¹;φ]` has stable `K₂ = 0`, the Mayer–Vietoris
factorization holds trivially after padding.  (`yaoseq6.tex` `thm:skewyao`, Step 1;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem yaoFactorization_of_stableK2Trivial (hL : LVH2GL3.StableK2Trivial (SkewLaurent S)) :
    YaoFactorization S := by
  intro n k hk
  obtain ⟨N₀, h₀, hk₀⟩ := hL n k hk
  have hN : N₀ ≤ N₀ + 2 := Nat.le_add_right N₀ 2
  have hp : projection (1 : SteinbergGroup (Fin (N₀ + 2)) (skewHalf S 1)) = 1 := map_one _
  have hg : elementaryMatrixUnitMap (ι := Fin (N₀ + 2)) (halfConst S 1) 1 = 1 := map_one _
  refine ⟨N₀ + 2, h₀.trans hN, 1, 1, 1, Nat.le_add_left 2 N₀, ?_, ?_⟩
  · rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb h₀ hN k, hk₀, map_one, map_one, map_one, mul_one]
  · exact (congrArg Subtype.val hp).trans hg.symm

/-- **Yao's factorization versus the endpoint.**  Given `GL_n(S) = E_n(S)` (lane 3c) and stable
`K₂ = 0` of both half rings (lane 3b), the factorization `YaoFactorization S` holds if and only if
`S[t,t⁻¹;φ]` has stable `K₂ = 0`.  (`yaoseq6.tex` `thm:skewyao`, Steps 1-2;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem yaoFactorization_iff_stableK2Trivial (hK1 : K1Statement S) (hHalf : HalfK2Statement S) :
    YaoFactorization S ↔ LVH2GL3.StableK2Trivial (SkewLaurent S) :=
  ⟨stableK2Trivial_of_yaoFactorization hK1 hHalf, yaoFactorization_of_stableK2Trivial⟩

end Equivalence

end GroupApproximation.Full.LVSkewLaurentK2
