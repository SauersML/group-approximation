import GroupApproximation.CharClass.ChernEvenPiece
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# The even mod-2 cohomology of a space as a graded ring

`CharClass/ChernEvenPiece.lean` supplies the pieces `H^{2n}(X;F₂)`, their product
and their unit.  What is added here is the *associativity* and *left unitality*
of that product, which are theorems about the Alexander–Whitney cup product
rather than bookkeeping, and the resulting `DirectSum.GRing` structure.

`evenGRing` is a `def` and not an `instance` on purpose: graded commutativity is a
further genuine theorem (the `⌣₁` chain homotopy), and
`CharClass/ChernEvenRingComm.lean` adds that one field, so the sole instance —
and the only `CommRing (EvenH X)` — is the commutative one declared there.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- **Left unitality**, transported. -/
theorem evenOne_evenMul {X : TopCat.{0}} {n : ℕ} (a : EvenPiece X n)
    (h : 2 * (0 + n) = 2 * n) :
    cohCast h (evenMul (evenOne X) a) = a := by
  show cohCast h (cohCast (two_mul_add 0 n) (cup (one X) a)) = a
  rw [one_cup, cohCast_cohCast, cohCast_cohCast]

/-- **Associativity**, transported. -/
theorem evenMul_assoc {X : TopCat.{0}} {i j k : ℕ}
    (a : EvenPiece X i) (b : EvenPiece X j) (c : EvenPiece X k)
    (h : 2 * (i + j + k) = 2 * (i + (j + k))) :
    cohCast h (evenMul (evenMul a b) c) = evenMul a (evenMul b c) := by
  show cohCast h (cohCast (two_mul_add (i + j) k)
      (cup (cohCast (two_mul_add i j) (cup a b)) c))
    = cohCast (two_mul_add i (j + k)) (cup a (cohCast (two_mul_add j k) (cup b c)))
  rw [cup_cohCast_left, cup_cohCast_right, cup_assoc, cohCast_cohCast, cohCast_cohCast,
    cohCast_cohCast, cohCast_cohCast]

/-! ## 3. The graded ring -/

/-- The graded ring structure on `n ↦ H^{2n}(X; F₂)`: everything except
commutativity, which needs the `⌣₁` chain homotopy and is added in
`CharClass/ChernEvenRingComm.lean`.  This is a `def` and not an `instance`
precisely so that the commutative structure there is the only instance. -/
def evenGRing (X : TopCat.{0}) : DirectSum.GRing (fun n : ℕ => EvenPiece X n) where
  mul a b := evenMul a b
  one := evenOne X
  mul_zero a := evenMul_zero a
  zero_mul b := zero_evenMul b
  mul_add a b c := evenMul_add a b c
  add_mul a b c := add_evenMul a b c
  one_mul a := by
    obtain ⟨n, a⟩ := a
    exact Sigma.ext (zero_add n)
      (heq_of_evenCast (by omega) _ _ (evenOne_evenMul a (by omega)))
  mul_one a := by
    obtain ⟨n, a⟩ := a
    exact Sigma.ext (add_zero n)
      (heq_of_evenCast (by omega) _ _ (evenMul_evenOne a (by omega)))
  mul_assoc a b c := by
    obtain ⟨i, a⟩ := a
    obtain ⟨j, b⟩ := b
    obtain ⟨k, c⟩ := c
    exact Sigma.ext (add_assoc i j k)
      (heq_of_evenCast (by omega) _ _ (evenMul_assoc a b c (by omega)))
  natCast n := (n : ZMod 2) • evenOne X
  natCast_zero := by simp
  natCast_succ n := by
    show ((n + 1 : ℕ) : ZMod 2) • evenOne X = ((n : ℕ) : ZMod 2) • evenOne X + evenOne X
    rw [Nat.cast_succ, add_smul, one_smul]
  intCast n := (n : ZMod 2) • evenOne X
  intCast_ofNat n := by
    show ((((n : ℕ) : ℤ)) : ZMod 2) • evenOne X = ((n : ℕ) : ZMod 2) • evenOne X
    rw [Int.cast_natCast]
  intCast_negSucc_ofNat n := by
    show ((Int.negSucc n : ℤ) : ZMod 2) • evenOne X = -(((n + 1 : ℕ) : ZMod 2) • evenOne X)
    rw [Int.cast_negSucc, neg_smul]
    norm_cast

end

end CharClass
end GroupApproximation
