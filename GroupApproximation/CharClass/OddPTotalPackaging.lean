import GroupApproximation.CharClass.OddPTotalPackagingMulSingle

/-!
# Packaging the reduced powers: `TotalReducedPowers p → EvenReducedPowers p`

The assembly.  The graded operations are `totalP` restricted to the even part, the total power is
`Ptot`, the junk-free classes are `good`, and each field of `OddPTotal.EvenReducedPowers` is one of
the lemmas of `OddPTotalPackaging{Defs,Good,Expand,Cartan,MulSingle}`:
* `natural`, `ptot_natural` — naturality of `ptotOf` through the degree projection;
* `shift`, `unstable` — `totalP_of_homogeneous`, `totalP_of_eq_zero`;
* `good_natural`, `good_two`, `good_of_components` — `isGood_map`, `isGoodPiece_two`, `isGood_of`;
* `cartan` — `totalP_cartan`;
* `mul_single` — `totalP_mul_single`;
* `zero_one`, `zero_cp`, `degree_two` — `unit_zero`, `zero_cp`, `top_two`, normalised by `μ^{-(d/2 − i)}`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

namespace TotalReducedPowers

variable {p : ℕ} (R : TotalReducedPowers p)

theorem totalP_map {X Y : TopCat.{0}} (f : X ⟶ Y) (i : ℕ) (x : TotalHOf (ZMod p) Y) :
    R.totalP X i (TotalHOf.map (ZMod p) f x) = TotalHOf.map (ZMod p) f (R.totalP Y i x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of d c =>
    show R.totalP X i (TotalHOf.map (ZMod p) f (TotalHOf.of (ZMod p) Y d c))
      = TotalHOf.map (ZMod p) f (R.totalP Y i (TotalHOf.of (ZMod p) Y d c))
    rw [TotalHOf.map_of, R.totalP_of, R.totalP_of, R.pieceP_apply, R.pieceP_apply]
    by_cases h : d % 2 = 0 ∧ 2 * i ≤ d
    · rw [if_pos h, if_pos h, R.ptotOf_natural, projDeg_map, map_smul']
    · rw [if_neg h, if_neg h, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- Reindexing a class `[D_j]` along an equality of indices, inside the ring. -/
theorem of_D_congr (X : TopCat.{0}) (q : ℕ) {j j' : ℕ} (h : j = j') (x : Hmod (ZMod p) X q) :
    TotalHOf.of (ZMod p) X (p * q - j) (R.D X q j x)
      = TotalHOf.of (ZMod p) X (p * q - j') (R.D X q j' x) := by
  subst h
  rfl

theorem ptotOf_one (X : TopCat.{0}) : ptotOf R.D X 0 (one X) = 1 := by
  rw [R.ptotOf_apply, show p * 0 + 1 = 1 by simp, Finset.sum_range_one, if_pos rfl]
  exact R.unit_zero X

theorem totalP_zero_one (X : TopCat.{0}) : R.totalP X 0 1 = 1 := by
  rw [← TotalHOf.of_one (ZMod p) X, R.totalP_of_eq X rfl 0 (le_refl 0), R.ptotOf_one,
    ← TotalHOf.of_one (ZMod p) X, show 0 + 2 * 0 * (p - 1) = 0 by simp, projDeg_of, if_pos rfl]
  simp

theorem totalP_zero_cp (hp : 2 ≤ p) (M : ℕ) (c : TotalPieceOf (ZMod p) (CPtop M) 2) :
    R.totalP (CPtop M) 0 (TotalHOf.of (ZMod p) (CPtop M) 2 c) = TotalHOf.of (ZMod p) (CPtop M) 2 c := by
  rw [R.totalP_of_eq (CPtop M) rfl 0 (by norm_num), projDeg_apply,
    show 2 + 2 * 0 * (p - 1) = 2 by simp, R.component_ptotOf, dif_pos ⟨by omega, by omega⟩,
    TotalHOf.of_cohCast, R.of_D_congr (CPtop M) 2 (show p * 2 - 2 = 2 * (p - 1) by omega),
    R.zero_cp, smul_smul, show 2 / 2 - 0 = 1 by norm_num, pow_one, R.μinv_mul, one_smul]

theorem totalP_degree_two (hp : 2 ≤ p) (X : TopCat.{0}) (c : TotalPieceOf (ZMod p) X 2) :
    R.totalP X 1 (TotalHOf.of (ZMod p) X 2 c) = TotalHOf.of (ZMod p) X 2 c ^ p := by
  rw [R.totalP_of_eq X rfl 1 (by norm_num), projDeg_apply, R.component_ptotOf,
    dif_pos ⟨by omega, by omega⟩, TotalHOf.of_cohCast,
    R.of_D_congr X 2 (show p * 2 - (2 + 2 * 1 * (p - 1)) = 0 by omega), R.top_two,
    show 2 / 2 - 1 = 0 by norm_num, pow_zero, one_smul]

/-- **The packaging.**  From the classes of the equivariant construction to the operations the
Step D producers consume. -/
def toEven (hp : 2 ≤ p) : EvenReducedPowers p where
  P X i := Gen.evenRestrictAdd (R.totalP X i) (fun x _ => R.totalP_isEven X i x)
  natural f i x := Subtype.ext (R.totalP_map f i x)
  shift X i d hd c := R.totalP_of_homogeneous X d i c
  unstable X i d hd c h :=
    Subtype.ext (R.totalP_of_eq_zero X i (fun h' => by have := h'.2; omega) c)
  Ptot X := R.Ptot X
  ptot_natural f x := Subtype.ext (R.totalPtot_map f x)
  Good X := R.good X
  good_natural f x hx := R.isGood_map f hx
  good_two X c := R.isGood_of X c (R.isGoodPiece_two X c hp)
  good_of_components X d hd c h := by
    refine R.isGood_of X c fun e he hg => ?_
    have hd2 : d % 2 = 0 := Nat.even_iff.mp hd
    have hc := h e he hg
    simp only [coe_Ptot, coe_evenOf] at hc
    rwa [R.totalPtot_of, R.piecePtot_apply, if_pos hd2] at hc
  cartan X i u v hu hv := by
    apply Subtype.ext
    simp only [Gen.coe_evenRestrictAdd, AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
    exact R.totalP_cartan X hp u.2 v.2 hu hv i
  mul_single X q hq z ν hz := by
    have hq2 : q % 2 = 0 := Nat.even_iff.mp hq
    simp only [coe_Ptot, coe_evenOf] at hz
    rw [R.totalPtot_of, R.piecePtot_apply, if_pos hq2] at hz
    refine ⟨R.μinv ^ (q / 2) * ν, fun i w => ?_⟩
    simp only [Gen.coe_evenRestrictAdd, Subring.coe_mul, coe_evenOf]
    exact R.totalP_mul_single X hp hq2 z ν hz i w.2
  zero_one X := Subtype.ext (R.totalP_zero_one X)
  zero_cp M c := Subtype.ext (R.totalP_zero_cp hp M c)
  degree_two X c := by
    apply Subtype.ext
    simp only [Gen.coe_evenRestrictAdd, SubmonoidClass.coe_pow, coe_evenOf]
    exact R.totalP_degree_two hp X c

end TotalReducedPowers

end

end OddPTotal

#audit_axioms OddPTotal.TotalReducedPowers.totalP_map
#audit_axioms OddPTotal.TotalReducedPowers.ptotOf_one
#audit_axioms OddPTotal.TotalReducedPowers.totalP_zero_cp
#audit_axioms OddPTotal.TotalReducedPowers.totalP_degree_two
#audit_axioms OddPTotal.TotalReducedPowers.toEven

end CharClass
end GroupApproximation
