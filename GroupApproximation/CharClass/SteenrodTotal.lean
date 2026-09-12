import GroupApproximation.CharClass.SteenrodSquare
import GroupApproximation.CharClass.ChernTotalRing

/-!
# The total Steenrod operation on `⨁_n H^n(X; F₂)`

`cc-wu`'s `ParityData` takes its Steenrod operation as a family of **additive
endomorphisms of one ring**, `SqH : ℕ → H →+ H`, not as a graded family
`H^n → H^{n+k}`.  This file assembles `cc-steenrod`'s graded `Sq k` into that
shape on `cc-projective`'s `TotalH X = ⨁_n H^n(X; F₂)`.

## What is here

* `SqH X k : TotalH X →+ TotalH X`, sending the degree-`n` piece to the
  degree-`k+n` piece by `Sq k`.  Additivity is inherited from `DirectSum`, so
  `cc-wu`'s `SqH` field is `SqH X` on the nose.
* `SqH_zero_apply` — `cc-wu`'s field of the same name.
* `SqH_of_eq_zero_of_lt` — instability in `cc-wu`'s form: `SqH j` kills every
  piece of degree below `j`.
* `Sq_pull` and `SqH_map` — naturality, at one degree and on the ring.

## What is not here yet

`cartanH` needs `cc-cartan`'s Cartan formula, and the line-class law
`Sq(y) = y + y²` for a degree-`2` class pulled back from `ℂP^{K-1}` needs one
input from `cc-projective` that has not landed: the vanishing of `H^3(ℂP^d; F₂)`.
Both are recorded with their exact statements in
`notes/lix-lane-reports/cc-steenrod.md` under NEEDS.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. Naturality of the graded square -/

/-- **`Sq^k` is natural.**  Pulling back a class and squaring is squaring and
pulling back. -/
theorem Sq_pull {X Y : TopCat.{0}} (f : X ⟶ Y) (k n : ℕ) (a : Hmod2 Y n) :
    Sq k (pull f n a) = pull f (k + n) (Sq k a) := by
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle a
  rw [pull_mk, Sq_mk, Sq_mk, pull_mk]
  refine cocycleClass_congr X (k + n) ?_ _ _
  unfold sqCochain
  exact (cochainCupI_naturality f (n - k) n n (k + n) φ φ).symm

/-! ## 2. The graded square as an additive map -/

/-- `Sq^k` on the degree-`n` piece, packaged additively. -/
def sqAdd (X : TopCat.{0}) (n k : ℕ) : TotalPiece X n →+ TotalPiece X (k + n) where
  toFun a := Sq k a
  map_zero' := map_zero (sqHomology X n k).hom
  map_add' a b := Sq_add k n a b

@[simp] theorem sqAdd_apply (X : TopCat.{0}) (n k : ℕ) (a : TotalPiece X n) :
    sqAdd X n k a = Sq k a := rfl

/-- Transporting a class along an equality of degrees does not move it in the
graded ring. -/
theorem of_cohCast {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (a : TotalPiece X m) :
    TotalH.of X m' (cohCast h a) = TotalH.of X m a := by
  subst h
  rw [cohCast_rfl]

/-! ## 3. The total operation -/

/-- **The total Steenrod operation.**  `SqH X k` is `cc-wu`'s `SqH k`: an
additive endomorphism of the whole ring `⨁_n H^n(X; F₂)`, raising degree by
`k`. -/
def SqH (X : TopCat.{0}) (k : ℕ) : TotalH X →+ TotalH X :=
  DirectSum.toAddMonoid (fun n => (TotalH.of X (k + n)).comp (sqAdd X n k))

@[simp] theorem SqH_of (X : TopCat.{0}) (k n : ℕ) (a : TotalPiece X n) :
    SqH X k (TotalH.of X n a) = TotalH.of X (k + n) (Sq k a) :=
  DirectSum.toAddMonoid_of (fun n => (TotalH.of X (k + n)).comp (sqAdd X n k)) n a

/-- **`cc-wu`'s `sqH_zero_apply`.** -/
theorem SqH_zero_apply (X : TopCat.{0}) (c : TotalH X) : SqH X 0 c = c := by
  induction c using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of n a =>
      show SqH X 0 (TotalH.of X n a) = TotalH.of X n a
      rw [SqH_of, Sq_zero n a]
      exact of_cohCast (Nat.zero_add n).symm a
  | add x y hx hy => rw [map_add, hx, hy]

/-- **Instability, in `cc-wu`'s form.**  `SqH j` kills every piece of degree
below `j`. -/
theorem SqH_of_eq_zero_of_lt (X : TopCat.{0}) (k n : ℕ) (hk : n < k)
    (a : TotalPiece X n) : SqH X k (TotalH.of X n a) = 0 := by
  rw [SqH_of, Sq_eq_zero_of_lt k n hk a, map_zero]

/-- **Naturality of the total operation.** -/
theorem SqH_map {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (c : TotalH Y) :
    SqH X k (TotalH.map f c) = TotalH.map f (SqH Y k c) := by
  induction c using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      show SqH X k (TotalH.map f (TotalH.of Y n a))
        = TotalH.map f (SqH Y k (TotalH.of Y n a))
      rw [TotalH.map_of, SqH_of, SqH_of, TotalH.map_of, Sq_pull]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The top square on a single piece, in ring form: `SqH n` of a degree-`n`
piece is its square. -/
theorem SqH_of_self (X : TopCat.{0}) (n : ℕ) (a : TotalPiece X n) :
    SqH X n (TotalH.of X n a) = TotalH.of X n a * TotalH.of X n a := by
  rw [SqH_of, Sq_self n a, TotalH.of_mul]

end

end Steenrod
end CharClass
end GroupApproximation
