import GroupApproximation.CharClass.CohomologyAssoc
import Mathlib.Algebra.DirectSum.Ring

/-!
# The cohomology of a space with coefficients in `K`, as a graded ring

```text
TotalHOf K X  :=  ⨁_{n : ℕ} H^n(X; K)
```

with multiplication the cup product and unit the class `1 ∈ H^0`.  This is the
coefficient-generic form of `ChernTotalRing`'s `TotalH X`, which stays the `F₂` spelling.

Over a general commutative ring the cup product is graded-commutative only up to the
Koszul sign, so the structure here is a `DirectSum.GRing` and **not** a `GCommRing`:
`mul_comm` is dropped, and it must not come back.  Two classes of which one has even degree
commute by `cup_comm_of_even_left` / `cup_comm_of_even_right` (`CupOneComm`); the element
level (`IsEven`, `mul_comm_of_isEven`) belongs to `CupOneTotal`.

The multiplication needs no degree transport: `cup` already has the signature
`A i → A j → A (i + j)` that `DirectSum.GRing` asks for.  The graded structure is the only
source of the ring, so `Semiring (TotalHOf K X)` has one route.

Names follow the coefficient convention: `K` explicit and first in the type formers and the
bundled maps, where no argument determines it.

## Main declarations

* `TotalPieceOf K X n`, `TotalHOf K X` — the pieces and the ring.
* `instGRingOf K X` — the single instance the ring comes from.
* `TotalHOf.of`, `TotalHOf.component`, `TotalHOf.component_of`, `TotalHOf.of_eq_zero_iff`,
  `TotalHOf.of_one`, `TotalHOf.of_mul` — the grading.
* `TotalHOf.map`, `TotalHOf.map_of` — pullback as a ring homomorphism.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- The degree-`n` piece of the cohomology ring with coefficients in `K`. -/
abbrev TotalPieceOf (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) : Type := Hmod K X n

namespace TotalHOf

/-- Classes in degrees with the same value are heterogeneously equal as soon as one
transports to the other. -/
theorem heq_of_cohCast {K : Type} [CommRing K] {X : TopCat.{0}} {m n : ℕ} (h : m = n)
    (a : Hmod K X m) (b : Hmod K X n) (hab : cohCast h a = b) : HEq a b := by
  subst h
  exact heq_of_eq hab

end TotalHOf

/-- **The cohomology of a space with coefficients in `K` is a graded ring.**  The
multiplication is the cup product with no transport, the unit is `1 ∈ H^0`, and
associativity and left unitality are `cup_assoc'` and `one_cup'`.  There is no `mul_comm`
field: over `K` it is false in odd degrees. -/
@[reducible]
instance instGRingOf (K : Type) [CommRing K] (X : TopCat.{0}) :
    DirectSum.GRing (fun n : ℕ => TotalPieceOf K X n) :=
  letI : GradedMonoid.GMul (fun n : ℕ => TotalPieceOf K X n) := ⟨fun a b => cup a b⟩
  letI : GradedMonoid.GOne (fun n : ℕ => TotalPieceOf K X n) := ⟨one (K := K) X⟩
  { mul := fun a b => cup a b
    one := one (K := K) X
    mul_zero := fun a => cup_zero a
    zero_mul := fun b => zero_cup b
    mul_add := fun a b c => cup_add_right a b c
    add_mul := fun a b c => cup_add_left a b c
    one_mul := fun a => by
      obtain ⟨n, a⟩ := a
      exact Sigma.ext (zero_add n)
        (TotalHOf.heq_of_cohCast (Nat.zero_add n).symm a (cup (one (K := K) X) a)
          (one_cup' a).symm).symm
    mul_one := fun a => by
      obtain ⟨n, a⟩ := a
      exact Sigma.ext (add_zero n) (heq_of_eq (cup_one a))
    mul_assoc := fun a b c => by
      obtain ⟨i, a⟩ := a
      obtain ⟨j, b⟩ := b
      obtain ⟨k, c⟩ := c
      exact Sigma.ext (add_assoc i j k)
        (TotalHOf.heq_of_cohCast (Nat.add_assoc i j k).symm (cup a (cup b c))
          (cup (cup a b) c) (cup_assoc' a b c).symm).symm
    natCast := fun n => (n : K) • one (K := K) X
    natCast_zero := by simp
    natCast_succ := fun n => by
      show ((n + 1 : ℕ) : K) • one (K := K) X = ((n : ℕ) : K) • one (K := K) X + one (K := K) X
      rw [Nat.cast_succ, add_smul, one_smul]
    intCast := fun n => (n : K) • one (K := K) X
    intCast_ofNat := fun n => by
      show ((((n : ℕ) : ℤ)) : K) • one (K := K) X = ((n : ℕ) : K) • one (K := K) X
      rw [Int.cast_natCast]
    intCast_negSucc_ofNat := fun n => by
      show ((Int.negSucc n : ℤ) : K) • one (K := K) X = -(((n + 1 : ℕ) : K) • one (K := K) X)
      rw [Int.cast_negSucc, neg_smul] }

/-- **The cohomology ring with coefficients in `K`**, `⨁_n H^n(X; K)`. -/
abbrev TotalHOf (K : Type) [CommRing K] (X : TopCat.{0}) : Type :=
  DirectSum ℕ (fun n : ℕ => TotalPieceOf K X n)

namespace TotalHOf

/-- The inclusion of the degree-`n` piece. -/
def of (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    TotalPieceOf K X n →+ TotalHOf K X :=
  DirectSum.of (fun n : ℕ => TotalPieceOf K X n) n

/-- The degree-`n` component. -/
def component (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    TotalHOf K X →+ TotalPieceOf K X n :=
  (DirectSum.component K ℕ (fun n : ℕ => TotalPieceOf K X n) n).toAddMonoidHom

@[simp] theorem component_of (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (a : TotalPieceOf K X n) : component K X n (of K X n a) = a := by
  show (DirectSum.of (fun n : ℕ => TotalPieceOf K X n) n a) n = a
  exact DirectSum.of_eq_same n a

/-- A class concentrated in one degree vanishes in the ring exactly when it vanishes in its
own degree. -/
theorem of_eq_zero_iff (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (a : TotalPieceOf K X n) : of K X n a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hc := congrArg (component K X n) h
    rwa [component_of, map_zero] at hc
  · intro h
    rw [h, map_zero]

@[simp] theorem of_one (K : Type) [CommRing K] (X : TopCat.{0}) :
    of K X 0 (one (K := K) X) = 1 := rfl

theorem of_mul (K : Type) [CommRing K] (X : TopCat.{0}) (m n : ℕ) (a : TotalPieceOf K X m)
    (b : TotalPieceOf K X n) : of K X (m + n) (cup a b) = of K X m a * of K X n b :=
  (DirectSum.of_mul_of a b).symm

/-- Pullback on a single degree, as an additive map. -/
def pullAdd (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    TotalPieceOf K Y n →+ TotalPieceOf K X n where
  toFun a := pull f n a
  map_zero' := pull_zero f n
  map_add' a b := pull_add f n a b

@[simp] theorem pullAdd_apply (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : TotalPieceOf K Y n) : pullAdd K f n a = pull f n a := rfl

/-- **Pullback as a ring homomorphism.** -/
def map (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TotalHOf K Y →+* TotalHOf K X :=
  DirectSum.toSemiring (fun n => (of K X n).comp (pullAdd K f n))
    (by
      show of K X 0 (pull f 0 (one (K := K) Y)) = 1
      rw [pull_one]
      exact of_one K X)
    (fun {m n} a b => by
      show of K X (m + n) (pull f (m + n) (cup a b))
        = of K X m (pull f m a) * of K X n (pull f n b)
      rw [pull_cup, of_mul])

@[simp] theorem map_of (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a : TotalPieceOf K Y n) : map K f (of K Y n a) = of K X n (pull f n a) :=
  DirectSum.toSemiring_of _ _ _ n a

end TotalHOf

end

end CharClass
end GroupApproximation
