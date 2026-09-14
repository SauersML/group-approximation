import GroupApproximation.GGT.VanKampen.CombMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's count with a budget of small faces

For a planar map every face of which has degree at least four, twice the number of edges plus six
is at most three times the number of vertices plus the number of faces of degree less than six:
`2E + 6 ≤ 3V + t`.  The faces sum to `2E` and each has degree at least `6` except the `t` small
ones, which have degree at least `4`, so `6F ≤ 2E + 2t`.  With `V − E + F = 2` this gives the
bound.

This is the count of the contact piece of Osin's Lemma 9.4 on the bipartite map of polygons and
objects, whose faces have even degree at least four once no two polygons join the same objects
along an empty two-gon.

Model test (hand).  A square, one inner face and the outer face, both of degree four: `V = 4`,
`E = 4`, `t = 2`, and `2·4 + 6 = 14 = 3·4 + 2`, so the bound is sharp there.

* `CombMap.six_mul_faceCount_le`: `6F ≤ 2E + 2t`.
* `CombMap.two_mul_edgeCount_add_six_le`: `2E + 6 ≤ 3V + t`.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe u

/-- **The faces with the small-face budget**: `6F ≤ 2E + 2t` when every face has degree at least
four. -/
theorem six_mul_faceCount_le (M : CombMap.{u}) (hfour : ∀ f : M.Face, 4 ≤ M.faceDegree f) :
    6 * M.faceCount ≤
      2 * M.edgeCount + 2 * (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card := by
  classical
  have hpt : ∀ f : M.Face,
      6 ≤ M.faceDegree f + 2 * (if M.faceDegree f < 6 then 1 else 0) := by
    intro f
    have := hfour f
    split_ifs with h <;> omega
  have hs : ∑ _f : M.Face, 6 ≤
      ∑ f : M.Face, (M.faceDegree f + 2 * (if M.faceDegree f < 6 then 1 else 0)) :=
    Finset.sum_le_sum fun f _ => hpt f
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    M.sum_faceDegree_eq_two_mul_edgeCount] at hs
  have hcard : ∑ f : M.Face, (if M.faceDegree f < 6 then 1 else 0) =
      (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card := by
    rw [Finset.card_filter]
  have hF : Fintype.card M.Face = M.faceCount := by
    rw [CombMap.faceCount, Nat.card_eq_fintype_card]
  rw [hcard, hF] at hs
  omega

/-- **Euler's count with a budget of small faces.**  On a planar map with every face of degree at
least four, `2E + 6 ≤ 3V + t`, where `t` counts the faces of degree less than six. -/
theorem two_mul_edgeCount_add_six_le (M : CombMap.{u}) (hM : M.IsPlanar)
    (hfour : ∀ f : M.Face, 4 ≤ M.faceDegree f) :
    2 * M.edgeCount + 6 ≤
      3 * M.vertexCount + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card := by
  have hE := M.euler_eq_two hM
  have hb := M.six_mul_faceCount_le hfour
  omega

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.six_mul_faceCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.two_mul_edgeCount_add_six_le
