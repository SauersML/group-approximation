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
  exact cohCast_self _ a

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
commutativity, which needs the `⌣₁` chain homotopy and is added conditionally
in `CharClass/ChernEvenRingComm.lean`.  This **is** the instance: `EvenH.map`
and every other plain semiring-level user need `GRing`/`GSemiring` now, and
commutativity is not yet available (it waits on `cc-steenrod`'s `cup_comm`).
Once it lands, `ChernEvenRingComm.gCommRing` upgrades this to `GCommRing` by
splicing `__ := evenGRing X`, so the two instance paths compute the identical
`mul`/`one` and there is no diamond.

The local `GMul`/`GOne` instances below exist only so that the `gnpow`/
`gnpow_zero'`/`gnpow_succ'` fields of `GradedMonoid.GMonoid` — which Lean fills
in from `GradedMonoid.gnpowRec` and needs `[GMul A] [GOne A]` to do so — can be
synthesized: with no ambient instance for `fun n => EvenPiece X n` at all, that
synthesis has nothing to find.  They agree with the `mul`/`one` fields on the
nose, so nothing downstream depends on which route computed a power. -/
@[reducible]
instance evenGRing (X : TopCat.{0}) : DirectSum.GRing (fun n : ℕ => EvenPiece X n) :=
  letI : GradedMonoid.GMul (fun n : ℕ => EvenPiece X n) := ⟨fun a b => evenMul a b⟩
  letI : GradedMonoid.GOne (fun n : ℕ => EvenPiece X n) := ⟨evenOne X⟩
  { mul := fun a b => evenMul a b
    one := evenOne X
    mul_zero := fun a => evenMul_zero a
    zero_mul := fun b => zero_evenMul b
    mul_add := fun a b c => evenMul_add a b c
    add_mul := fun a b c => add_evenMul a b c
    one_mul := fun a => by
      obtain ⟨n, a⟩ := a
      have hdeg : 2 * (0 + n) = 2 * n := by omega
      exact Sigma.ext (zero_add n)
        (heq_of_evenCast hdeg (evenMul (evenOne X) a) a (evenOne_evenMul a hdeg))
    mul_one := fun a => by
      obtain ⟨n, a⟩ := a
      have hdeg : 2 * (n + 0) = 2 * n := by omega
      exact Sigma.ext (add_zero n)
        (heq_of_evenCast hdeg (evenMul a (evenOne X)) a (evenMul_evenOne a hdeg))
    mul_assoc := fun a b c => by
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      obtain ⟨k, c⟩ := c
      have hdeg : 2 * (i + j + k) = 2 * (i + (j + k)) := by omega
      exact Sigma.ext (add_assoc i j k)
        (heq_of_evenCast hdeg (evenMul (evenMul a b) c) (evenMul a (evenMul b c))
          (evenMul_assoc a b c hdeg))
    natCast := fun n => (n : ZMod 2) • evenOne X
    natCast_zero := by simp
    natCast_succ := fun n => by
      show ((n + 1 : ℕ) : ZMod 2) • evenOne X = ((n : ℕ) : ZMod 2) • evenOne X + evenOne X
      rw [Nat.cast_succ, add_smul, one_smul]
    intCast := fun n => (n : ZMod 2) • evenOne X
    intCast_ofNat := fun n => by
      show ((((n : ℕ) : ℤ)) : ZMod 2) • evenOne X = ((n : ℕ) : ZMod 2) • evenOne X
      rw [Int.cast_natCast]
    intCast_negSucc_ofNat := fun n => by
      show ((Int.negSucc n : ℤ) : ZMod 2) • evenOne X = -(((n + 1 : ℕ) : ZMod 2) • evenOne X)
      rw [Int.cast_negSucc, neg_smul] }

end

end CharClass
end GroupApproximation
