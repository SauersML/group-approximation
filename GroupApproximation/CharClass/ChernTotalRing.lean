import GroupApproximation.CharClass.CohomologyAssoc
import GroupApproximation.CharClass.SteenrodCupOne
import Mathlib.Algebra.DirectSum.Ring

/-!
# The mod-2 cohomology of a space as a commutative graded ring

```text
TotalH X  :=  ⨁_{n : ℕ} H^n(X; F₂)
```

with multiplication the cup product and unit the class `1 ∈ H^0`.  Mod 2 there
are **no Koszul signs in any degree**, so this is commutative outright, and the
multiplication needs no degree transport at all: `cup` already has the signature
`A i → A j → A (i + j)` that `DirectSum.GCommRing` asks for.

This replaces the earlier even-degree ring `EvenH = ⨁_n H^{2n}`.  Two reasons.
It is what cc-wu's `ParityData` has to be instantiated on, since that carries
generators of degree 1 and 5 and so cannot live in the even part.  And it is
*simpler*: every `cohCast` in the even construction came from
`2 * m + 2 * n = 2 * (m + n)` and disappears here.

It also settles an instance problem.  With an even ring plus a commutativity
*hypothesis*, `TotalH X` acquired a `Semiring` by two syntactically different
routes — `DirectSum.semiring` from the graded structure and
`CommRing.toCommSemiring.toSemiring` from the hypothesis — and every type
mentioning the ring pinned one of them at elaboration, so locally written
statements and imported lemmas disagreed.  Here the graded structure is the only
source of the ring, so the two routes coincide by projection.

## Main declarations

* `TotalH X` — the ring; `instGCommRing` is the single instance it comes from.
* `TotalH.of`, `TotalH.component`, `TotalH.of_eq_zero_iff` — the grading, and the
  fact that a class concentrated in one degree vanishes in the ring exactly when
  it vanishes in its own degree.
* `TotalH.map` — pullback as a ring homomorphism.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- The degree-`n` piece. -/
abbrev TotalPiece (X : TopCat.{0}) (n : ℕ) : Type := Hmod2 X n

/-- Classes in degrees with the same value are heterogeneously equal as soon as one
transports to the other. -/
theorem heq_of_cohCast {X : TopCat.{0}} {m n : ℕ} (h : m = n)
    (a : Hmod2 X m) (b : Hmod2 X n) (hab : cohCast h a = b) : HEq a b := by
  subst h
  exact heq_of_eq hab

/-- **The mod-2 cohomology of a space is a commutative graded ring.**  The
multiplication is the cup product with no transport, the unit is `1 ∈ H^0`,
associativity and left unitality are `cup_assoc'` and `one_cup'`, and
commutativity is `cup_comm`, which holds in all degrees because mod 2 there is no
sign. -/
@[reducible]
instance instGCommRing (X : TopCat.{0}) :
    DirectSum.GCommRing (fun n : ℕ => TotalPiece X n) :=
  letI : GradedMonoid.GMul (fun n : ℕ => TotalPiece X n) := ⟨fun a b => cup a b⟩
  letI : GradedMonoid.GOne (fun n : ℕ => TotalPiece X n) := ⟨one X⟩
  { mul := fun a b => cup a b
    one := one X
    mul_zero := fun a => cup_zero a
    zero_mul := fun b => zero_cup b
    mul_add := fun a b c => cup_add_right a b c
    add_mul := fun a b c => cup_add_left a b c
    one_mul := fun a => by
      obtain ⟨n, a⟩ := a
      exact Sigma.ext (zero_add n)
        (heq_of_cohCast (Nat.zero_add n).symm a (cup (one X) a) (one_cup' a).symm).symm
    mul_one := fun a => by
      obtain ⟨n, a⟩ := a
      exact Sigma.ext (add_zero n) (heq_of_eq (cup_one a))
    mul_assoc := fun a b c => by
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      obtain ⟨k, c⟩ := c
      exact Sigma.ext (add_assoc i j k)
        (heq_of_cohCast (Nat.add_assoc i j k).symm (cup a (cup b c)) (cup (cup a b) c)
          (cup_assoc' a b c).symm).symm
    mul_comm := fun a b => by
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      exact Sigma.ext (Nat.add_comm i j)
        (heq_of_cohCast (Nat.add_comm j i) (cup b a) (cup a b) (cup_comm a b).symm).symm
    natCast := fun n => (n : ZMod 2) • one X
    natCast_zero := by simp
    natCast_succ := fun n => by
      show ((n + 1 : ℕ) : ZMod 2) • one X = ((n : ℕ) : ZMod 2) • one X + one X
      rw [Nat.cast_succ, add_smul, one_smul]
    intCast := fun n => (n : ZMod 2) • one X
    intCast_ofNat := fun n => by
      show ((((n : ℕ) : ℤ)) : ZMod 2) • one X = ((n : ℕ) : ZMod 2) • one X
      rw [Int.cast_natCast]
    intCast_negSucc_ofNat := fun n => by
      show ((Int.negSucc n : ℤ) : ZMod 2) • one X = -(((n + 1 : ℕ) : ZMod 2) • one X)
      rw [Int.cast_negSucc, neg_smul] }

/-- **The mod-2 cohomology ring** `⨁_n H^n(X; F₂)`. -/
abbrev TotalH (X : TopCat.{0}) : Type := DirectSum ℕ (fun n : ℕ => TotalPiece X n)

/-- The inclusion of the degree-`n` piece. -/
def TotalH.of (X : TopCat.{0}) (n : ℕ) : TotalPiece X n →+ TotalH X :=
  DirectSum.of (fun n : ℕ => TotalPiece X n) n

/-- The degree-`n` component. -/
def TotalH.component (X : TopCat.{0}) (n : ℕ) : TotalH X →+ TotalPiece X n :=
  (DirectSum.component (ZMod 2) ℕ (fun n : ℕ => TotalPiece X n) n).toAddMonoidHom

@[simp] theorem TotalH.component_of (X : TopCat.{0}) (n : ℕ) (a : TotalPiece X n) :
    TotalH.component X n (TotalH.of X n a) = a := by
  show (DirectSum.of (fun n : ℕ => TotalPiece X n) n a) n = a
  exact DirectSum.of_eq_same n a

/-- A class concentrated in one degree vanishes in the ring exactly when it
vanishes in its own degree.  This is what turns a nonvanishing top Chern class in
`H^{2r}` into a statement about the ring, and back. -/
theorem TotalH.of_eq_zero_iff (X : TopCat.{0}) (n : ℕ) (a : TotalPiece X n) :
    TotalH.of X n a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hc := congrArg (TotalH.component X n) h
    rwa [TotalH.component_of, map_zero] at hc
  · intro h
    rw [h, map_zero]

@[simp] theorem TotalH.of_one (X : TopCat.{0}) : TotalH.of X 0 (one X) = 1 := rfl

theorem TotalH.of_mul (X : TopCat.{0}) (m n : ℕ) (a : TotalPiece X m) (b : TotalPiece X n) :
    TotalH.of X (m + n) (cup a b) = TotalH.of X m a * TotalH.of X n b :=
  (DirectSum.of_mul_of a b).symm

/-- Pullback on a single degree, as an additive map. -/
def pullAdd {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) : TotalPiece Y n →+ TotalPiece X n where
  toFun a := pull f n a
  map_zero' := pull_zero f n
  map_add' a b := pull_add f n a b

@[simp] theorem pullAdd_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : TotalPiece Y n) :
    pullAdd f n a = pull f n a := rfl

/-- **Pullback as a ring homomorphism.** -/
def TotalH.map {X Y : TopCat.{0}} (f : X ⟶ Y) : TotalH Y →+* TotalH X :=
  DirectSum.toSemiring (fun n => (TotalH.of X n).comp (pullAdd f n))
    (by
      show TotalH.of X 0 (pull f 0 (one Y)) = 1
      rw [pull_one]
      exact TotalH.of_one X)
    (fun {m n} a b => by
      show TotalH.of X (m + n) (pull f (m + n) (cup a b))
        = TotalH.of X m (pull f m a) * TotalH.of X n (pull f n b)
      rw [pull_cup, TotalH.of_mul])

@[simp] theorem TotalH.map_of {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : TotalPiece Y n) :
    TotalH.map f (TotalH.of Y n a) = TotalH.of X n (pull f n a) :=
  DirectSum.toSemiring_of _ _ _ n a

end

end CharClass
end GroupApproximation
