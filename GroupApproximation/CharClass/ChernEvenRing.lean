import GroupApproximation.CharClass.CohomologyBasic
import Mathlib.Algebra.DirectSum.Ring

/-!
# The even mod-2 cohomology of a space as a commutative ring

Chern classes are defined by a polynomial relation, so they need a *ring* to live
in — `Polynomial` and `PowerBasis` do not accept a family of groups indexed by a
degree.  This file packages

```text
EvenH X  :=  ⨁_{n : ℕ} H^{2n}(X; F₂)
```

as an honest `CommRing`, with multiplication the cup product and unit the class
`1 ∈ H^0`.  Restricting to even degrees is exactly what makes the ring
**commutative** with no signs and no `GradedMonoid` sign bookkeeping: mod 2 the
Koszul sign is invisible, and the degree of a product of even classes is again
even.

Nothing is lost by the restriction: Leray–Hirsch splits `H^k(P(E))` as
`⨁_{i<r} H^{k-2i}(X) ξ^i` with `ξ` of degree 2, so the even part of `H^*(P(E))`
is the free `EvenH X`-module on `1, ξ, …, ξ^{r-1}`, and every Chern class
`γ_i(E) ∈ H^{2i}(X)` is even by construction.

## Main declarations

* `EvenPiece X n` — `H^{2n}(X; F₂)`.
* `EvenH X` — the direct sum, a `CommRing`.
* `EvenH.of` — the inclusion of the degree-`n` piece, and `EvenH.component` its
  left inverse, so a class is zero in `EvenH X` iff it is zero in its own degree.
* `EvenH.map f` — the pullback along `f : X ⟶ Y`, a ring homomorphism, functorial.

## Interface consumed

From `CharClass/CohomologyBasic.lean` (lane `cc-cohom-api`): `Hmod2`, `cohCast`
and its laws, `cup`, `one`, `pull`, plus the three graded-ring axioms
`cup_assoc`, `cup_comm`, `one_cup`.  The first and third are strict at cochain
level (Alexander–Whitney); the second is the mod-2 commutativity coming from the
`⌣₁` chain homotopy.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. Moving a cup product past a degree cast -/

theorem cup_cohCast_left {X : TopCat.{0}} {p p' q : ℕ} (h : p = p') (h' : p + q = p' + q)
    (a : Hmod2 X p) (b : Hmod2 X q) :
    cup (cohCast h a) b = cohCast h' (cup a b) := by
  subst h; rfl

theorem cup_cohCast_right {X : TopCat.{0}} {p q q' : ℕ} (h : q = q') (h' : p + q = p + q')
    (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a (cohCast h b) = cohCast h' (cup a b) := by
  subst h; rfl

/-- Two transports along (necessarily equal) proofs of the same degree identity
agree; this is definitional proof irrelevance, and it is what lets every
associativity chase below finish by `rfl`. -/
theorem cohCast_congr {X : TopCat.{0}} {m n : ℕ} (h h' : m = n) (a : Hmod2 X m) :
    cohCast h a = cohCast h' a := rfl

theorem cohCast_self {X : TopCat.{0}} {m : ℕ} (h : m = m) (a : Hmod2 X m) :
    cohCast h a = a := rfl

/-! ## 2. The even pieces -/

/-- The degree-`2n` part of mod-2 cohomology. -/
abbrev EvenPiece (X : TopCat.{0}) (n : ℕ) : Type := Hmod2 X (2 * n)

/-- The product of two even classes, landing in the right even degree. -/
def evenMul {X : TopCat.{0}} {m n : ℕ} (a : EvenPiece X m) (b : EvenPiece X n) :
    EvenPiece X (m + n) :=
  cohCast (by omega) (cup a b)

/-- The unit of `EvenH`.  Note `2 * 0` reduces to `0`, so no transport is needed. -/
def evenOne (X : TopCat.{0}) : EvenPiece X 0 := one X

/-- Two even classes in degrees with the same double are heterogeneously equal as
soon as one transports to the other. -/
theorem heq_of_evenCast {X : TopCat.{0}} {m n : ℕ} (h : 2 * m = 2 * n)
    (a : EvenPiece X m) (b : EvenPiece X n) (hab : cohCast h a = b) : HEq a b := by
  have hmn : m = n := by omega
  subst hmn
  exact heq_of_eq hab

@[simp] theorem evenMul_zero {X : TopCat.{0}} {m n : ℕ} (a : EvenPiece X m) :
    evenMul a (0 : EvenPiece X n) = 0 := by
  simp [evenMul]

@[simp] theorem zero_evenMul {X : TopCat.{0}} {m n : ℕ} (b : EvenPiece X n) :
    evenMul (0 : EvenPiece X m) b = 0 := by
  simp [evenMul]

theorem evenMul_add {X : TopCat.{0}} {m n : ℕ} (a : EvenPiece X m) (b c : EvenPiece X n) :
    evenMul a (b + c) = evenMul a b + evenMul a c := by
  simp [evenMul, cup_add_right]

theorem add_evenMul {X : TopCat.{0}} {m n : ℕ} (a b : EvenPiece X m) (c : EvenPiece X n) :
    evenMul (a + b) c = evenMul a c + evenMul b c := by
  simp [evenMul, cup_add_left]

/-! ## 3. The graded commutative ring structure -/

instance instGCommRing (X : TopCat.{0}) :
    DirectSum.GCommRing (fun n : ℕ => EvenPiece X n) where
  mul a b := evenMul a b
  one := evenOne X
  mul_zero a := evenMul_zero a
  zero_mul b := zero_evenMul b
  mul_add a b c := evenMul_add a b c
  add_mul a b c := add_evenMul a b c
  one_mul a := by
    refine Sigma.ext (zero_add a.fst) (heq_of_evenCast (by omega) _ _ ?_)
    show cohCast _ (evenMul (evenOne X) a.snd) = a.snd
    rw [evenMul, evenOne, cohCast_cohCast]
    rw [← one_cup a.snd]
    exact cohCast_congr _ _ _
  mul_one a := by
    refine Sigma.ext (add_zero a.fst) (heq_of_evenCast (by omega) _ _ ?_)
    show cohCast _ (evenMul a.snd (evenOne X)) = a.snd
    rw [evenMul, evenOne, cohCast_cohCast, cup_one]
    rfl
  mul_assoc a b c := by
    refine Sigma.ext (add_assoc a.fst b.fst c.fst) (heq_of_evenCast (by omega) _ _ ?_)
    show cohCast _ (evenMul (evenMul a.snd b.snd) c.snd)
      = evenMul a.snd (evenMul b.snd c.snd)
    rw [evenMul, evenMul, evenMul, evenMul,
      cup_cohCast_left (by omega) (by omega), cup_cohCast_right (by omega) (by omega),
      cohCast_cohCast, cohCast_cohCast, cohCast_cohCast,
      ← cup_assoc a.snd b.snd c.snd, cohCast_cohCast]
    exact cohCast_congr _ _ _
  mul_comm a b := by
    refine Sigma.ext (Nat.add_comm a.fst b.fst) (heq_of_evenCast (by omega) _ _ ?_)
    show cohCast _ (evenMul a.snd b.snd) = evenMul b.snd a.snd
    rw [evenMul, evenMul, cohCast_cohCast, ← cup_comm a.snd b.snd, cohCast_cohCast]
    exact cohCast_congr _ _ _
  natCast n := (n : ZMod 2) • evenOne X
  natCast_zero := by simp
  natCast_succ n := by
    show ((n + 1 : ℕ) : ZMod 2) • evenOne X = (n : ZMod 2) • evenOne X + _
    rw [Nat.cast_succ, add_smul, one_smul]
    rfl
  intCast n := (n : ZMod 2) • evenOne X
  intCast_ofNat n := by
    show ((((n : ℕ) : ℤ)) : ZMod 2) • evenOne X = ((n : ℕ) : ZMod 2) • evenOne X
    rw [Int.cast_natCast]
  intCast_negSucc_ofNat n := by
    show ((Int.negSucc n : ℤ) : ZMod 2) • evenOne X = -(((n + 1 : ℕ) : ZMod 2) • evenOne X)
    rw [Int.cast_negSucc, neg_smul]
    congr 1
    push_cast
    ring

/-- **The even mod-2 cohomology ring** `⨁_n H^{2n}(X; F₂)`. -/
abbrev EvenH (X : TopCat.{0}) : Type := DirectSum ℕ (fun n : ℕ => EvenPiece X n)

instance instCommRingEvenH (X : TopCat.{0}) : CommRing (EvenH X) :=
  DirectSum.commRing (fun n : ℕ => EvenPiece X n)

/-! ## 4. Degrees -/

/-- The inclusion of the degree-`n` piece into the even cohomology ring. -/
def EvenH.of (X : TopCat.{0}) (n : ℕ) : EvenPiece X n →+ EvenH X :=
  DirectSum.of (fun n : ℕ => EvenPiece X n) n

/-- The degree-`n` component of an even cohomology class. -/
def EvenH.component (X : TopCat.{0}) (n : ℕ) : EvenH X →+ EvenPiece X n :=
  (DirectSum.component (ZMod 2) ℕ (fun n : ℕ => EvenPiece X n) n).toAddMonoidHom

@[simp] theorem EvenH.component_of (X : TopCat.{0}) (n : ℕ) (a : EvenPiece X n) :
    EvenH.component X n (EvenH.of X n a) = a := by
  simp [EvenH.component, EvenH.of, DirectSum.component]

/-- A class of a single degree is zero in the ring exactly when it is zero. -/
theorem EvenH.of_eq_zero_iff (X : TopCat.{0}) (n : ℕ) (a : EvenPiece X n) :
    EvenH.of X n a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg (EvenH.component X n) h
    simpa using this
  · intro h
    rw [h, map_zero]

@[simp] theorem EvenH.of_one (X : TopCat.{0}) : EvenH.of X 0 (evenOne X) = 1 :=
  rfl

theorem EvenH.of_mul (X : TopCat.{0}) (m n : ℕ) (a : EvenPiece X m) (b : EvenPiece X n) :
    EvenH.of X (m + n) (evenMul a b) = EvenH.of X m a * EvenH.of X n b :=
  (DirectSum.of_mul_of a b).symm

end

end CharClass
end GroupApproximation
