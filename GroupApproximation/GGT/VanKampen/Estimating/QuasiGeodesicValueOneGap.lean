import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.OsinTheorem54SepSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# A value-one gap of a quasi-geodesic word is short

Osin (math/0411039v3, §9), proof of Lemma 9.4.  The sides of a component polygon are counted in
classes, and consecutive sides along one relator cell or one section of `∂Δ` lie in one class.
The gap between two consecutive sides of a class is a subword of a `(λ, c)`-quasi-geodesic word
with value one.  Its two ends are the same vertex, so the quasi-geodesic inequality bounds its
length by `c / λ`.

* `IsLambdaCQuasiGeodesicWord.length_le_of_listVal_eq_one`: a value-one subword
  `(w.drop i).take m` of a `(λ, c)`-quasi-geodesic word `w` has `λ m ≤ c`.
* `IsLambdaCQuasiGeodesicWord.le_ceil_of_listVal_eq_one`: for `0 < λ`, `m ≤ ⌈c / λ⌉₊`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w

open GroupApproximation.WordMetric

/-- **A value-one subword of a quasi-geodesic word is short.**  If `(w.drop i).take m` has value
one, then vertices `i` and `i + m` of `w` coincide, and the quasi-geodesic inequality at
`(i, i + m)` reads `λ m - c ≤ 0`. -/
theorem IsLambdaCQuasiGeodesicWord.length_le_of_listVal_eq_one {G : Type u} [Group G]
    {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ} {w : List (RelLetter G Lambda)}
    (h : IsLambdaCQuasiGeodesicWord D lambda c w) {i m : ℕ} (him : i + m ≤ w.length)
    (hval : RelLetter.listVal ((w.drop i).take m) = 1) : lambda * m ≤ c := by
  have hquasi : lambda * ((i + m - i : ℕ) : ℝ) - c ≤
      ((wordDist D.alphabet.carrier (GGT.OsinComponents.vertex 1 w i)
        (GGT.OsinComponents.vertex 1 w (i + m)) : ℕ) : ℝ) :=
    h.2 i (i + m) (Nat.le_add_right i m) him
  have hvertex : GGT.OsinComponents.vertex 1 w (i + m) = GGT.OsinComponents.vertex 1 w i := by
    rw [GGT.OsinComponents.vertex_eq_mul_listVal_take,
      GGT.OsinComponents.vertex_eq_mul_listVal_take, List.take_add,
      HullSC.RelWord.listVal_append, hval, mul_one]
  rw [hvertex, wordDist_self, Nat.add_sub_cancel_left, Nat.cast_zero] at hquasi
  linarith

/-- **The gap bound in letters.**  For `0 < λ`, a value-one subword of a `(λ, c)`-quasi-geodesic
word has at most `⌈c / λ⌉₊` letters. -/
theorem IsLambdaCQuasiGeodesicWord.le_ceil_of_listVal_eq_one {G : Type u} [Group G]
    {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ} {w : List (RelLetter G Lambda)}
    (h : IsLambdaCQuasiGeodesicWord D lambda c w) (hlambda : 0 < lambda) {i m : ℕ}
    (him : i + m ≤ w.length) (hval : RelLetter.listVal ((w.drop i).take m) = 1) :
    m ≤ ⌈c / lambda⌉₊ := by
  have hle := h.length_le_of_listVal_eq_one him hval
  have hm : (m : ℝ) ≤ c / lambda := by
    rw [le_div_iff₀ hlambda]
    linarith [mul_comm lambda (m : ℝ)]
  exact_mod_cast hm.trans (Nat.le_ceil _)

#audit_axioms
  GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.length_le_of_listVal_eq_one
#audit_axioms
  GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.le_ceil_of_listVal_eq_one

end GroupApproximation.GGT.VanKampen
