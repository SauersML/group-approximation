import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZero

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-
**Tail commutes with internal cofaces.** For `y` away from the apex, the
normalized tail of `cofaceTop (k+1) (j+1) y` is the `j`-th coface of the
normalized tail of `y`.
-/
theorem coneTail_cofaceTop_succ {k : ℕ} (j : Fin (k + 1 + 1)) (y : Delta (k + 1))
    (hy : (y : Fin (k + 1 + 1) → ℝ) 0 ≠ 1) :
    coneTail (cofaceTop (k + 1) j.succ y) = cofaceTop k j (coneTail y) := by
  unfold cofaceTop;
  ext i; simp +decide;
  by_cases h : ( stdSimplex.map j.succ.succAbove y : Fin ( k + 1 + 1 + 1 ) → ℝ ) 0 = 1 <;> simp_all +decide [ coneTail_apply ];
  · simp_all +decide [ FunOnFinite.linearMap_apply_apply ];
    rw [ Finset.sum_eq_single 0 ] at h <;> simp_all +decide;
    intro b hb hb'; rw [ Fin.succAbove ] at hb; aesop;
  · simp +decide [ FunOnFinite.linearMap_apply_apply, coneTail_apply y hy ] at *;
    rw [ ← Finset.sum_div _ _ _, show ( Finset.filter ( fun x => j.succ.succAbove x = 0 ) Finset.univ : Finset ( Fin ( k + 1 + 1 ) ) ) = { 0 } from ?_, show ( Finset.filter ( fun x => j.succ.succAbove x = i.succ ) Finset.univ : Finset ( Fin ( k + 1 + 1 ) ) ) = Finset.image ( fun x => x.succ ) ( Finset.filter ( fun x => j.succAbove x = i ) Finset.univ ) from ?_ ] <;> norm_num;
    · ext x; simp +decide;
      cases x using Fin.inductionOn <;> simp +decide [ Fin.succ_succAbove_succ ];
      exact ne_of_lt ( Fin.succ_pos _ );
    · grind +suggestions
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
