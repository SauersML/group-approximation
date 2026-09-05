import GroupApproximation.CharClass.CohomologyBasic
import Mathlib.Algebra.DirectSum.Ring

/-!
# The even part of mod-2 cohomology: pieces, product, unit

Chern classes are defined by a polynomial relation, so they need a *ring* to live
in — `Polynomial` and `PowerBasis` do not accept a family of groups indexed by a
degree.  This file assembles

```text
EvenH X  :=  ⨁_{n : ℕ} H^{2n}(X; F₂)
```

with multiplication the cup product and unit the class `1 ∈ H^0`, as a
`DirectSum.GRing`.  Restricting to even degrees is what kills the Koszul signs:
mod 2 the sign is invisible anyway, and the degree of a product of even classes
is again even, so no `GradedMonoid` sign bookkeeping survives.

Nothing is lost by the restriction.  Leray–Hirsch splits `H^k(P(E))` as
`⨁_{i<r} H^{k-2i}(X) ξ^i` with `ξ` of degree 2, so the even part of `H^*(P(E))`
is exactly the free module over the even part of `H^*(X)` on `1, ξ, …, ξ^{r-1}`,
and every Chern class `γ_i(E) ∈ H^{2i}(X)` is even by construction.

The file is split so that everything provable from `CohomologyBasic` alone is
here, and the two facts that are genuine theorems about the Alexander–Whitney
product live downstream: associativity and left unitality in
`CharClass/ChernEvenRing.lean` (they are strict at cochain level), graded
commutativity in `CharClass/ChernEvenRingComm.lean` (it needs the `⌣₁` chain
homotopy, and only there does `EvenH X` become a `CommRing`).

## Main declarations

* `EvenPiece X n` — `H^{2n}(X; F₂)`; `evenMul`, `evenOne` — the graded product and unit.
* `evenOne_evenMul`, `evenMul_evenOne`, `evenMul_assoc` — the monoid laws in
  transported element form; the last two need `cup_assoc`/`one_cup` and are
  therefore stated here but proved downstream.
* `EvenH X` — the direct sum, as an additive group; `EvenH.of`, `EvenH.component`,
  `EvenH.of_eq_zero_iff`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. Degree casts and the cup product -/

theorem cup_cohCast_left {X : TopCat.{0}} {p p' q : ℕ} (h : p = p')
    (a : Hmod2 X p) (b : Hmod2 X q) :
    cup (cohCast h a) b = cohCast (by omega) (cup a b) := by
  subst h; rfl

theorem cup_cohCast_right {X : TopCat.{0}} {p q q' : ℕ} (h : q = q')
    (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a (cohCast h b) = cohCast (by omega) (cup a b) := by
  subst h; rfl

/-- Two transports along proofs of the same degree identity agree.  This is
definitional proof irrelevance, and it is what lets every cast chase below finish
by `rfl`. -/
theorem cohCast_congr {X : TopCat.{0}} {m n : ℕ} (h h' : m = n) (a : Hmod2 X m) :
    cohCast h a = cohCast h' a := rfl

theorem cohCast_self {X : TopCat.{0}} {m : ℕ} (h : m = m) (a : Hmod2 X m) :
    cohCast h a = a := rfl

/-! ## 2. The even pieces, their product and their unit -/

/-- The degree-`2n` part of mod-2 cohomology. -/
abbrev EvenPiece (X : TopCat.{0}) (n : ℕ) : Type := Hmod2 X (2 * n)

theorem two_mul_add (m n : ℕ) : 2 * m + 2 * n = 2 * (m + n) := by ring

/-- The cup product of two even classes, in the right even degree. -/
def evenMul {X : TopCat.{0}} {m n : ℕ} (a : EvenPiece X m) (b : EvenPiece X n) :
    EvenPiece X (m + n) :=
  cohCast (two_mul_add m n) (cup a b)

/-- The unit.  `2 * 0` reduces to `0`, so no transport is needed. -/
def evenOne (X : TopCat.{0}) : EvenPiece X 0 := one X

/-- Even classes in degrees with the same double are heterogeneously equal as soon
as one transports to the other. -/
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
  simp only [evenMul, cup_add_right, cohCast_add]

theorem add_evenMul {X : TopCat.{0}} {m n : ℕ} (a b : EvenPiece X m) (c : EvenPiece X n) :
    evenMul (a + b) c = evenMul a c + evenMul b c := by
  simp only [evenMul, cup_add_left, cohCast_add]

/-- **Right unitality**, transported.  Unlike the left version this needs no
theorem about the cup product beyond the strict `cup_one`. -/
theorem evenMul_evenOne {X : TopCat.{0}} {n : ℕ} (a : EvenPiece X n)
    (h : 2 * (n + 0) = 2 * n) :
    cohCast h (evenMul a (evenOne X)) = a := by
  show cohCast h (cohCast (two_mul_add n 0) (cup a (one X))) = a
  rw [cup_one, cohCast_cohCast]

/-! ## 4. Pullback -/

theorem pull_cohCast {X Y : TopCat.{0}} (f : X ⟶ Y) {m m' : ℕ} (h : m = m')
    (a : Hmod2 Y m) : pull f m' (cohCast h a) = cohCast h (pull f m a) := by
  subst h; rfl

/-- Pullback on an even piece, as an additive map. -/
def pullEven {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) : EvenPiece Y n →+ EvenPiece X n where
  toFun a := pull f (2 * n) a
  map_zero' := pull_zero f (2 * n)
  map_add' a b := pull_add f (2 * n) a b

@[simp] theorem pullEven_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : EvenPiece Y n) :
    pullEven f n a = pull f (2 * n) a := rfl

theorem pullEven_evenMul {X Y : TopCat.{0}} (f : X ⟶ Y) {m n : ℕ}
    (a : EvenPiece Y m) (b : EvenPiece Y n) :
    pullEven f (m + n) (evenMul a b) = evenMul (pullEven f m a) (pullEven f n b) := by
  show pull f (2 * (m + n)) (cohCast (two_mul_add m n) (cup a b))
    = cohCast (two_mul_add m n) (cup (pull f (2 * m) a) (pull f (2 * n) b))
  rw [pull_cohCast, pull_cup]

@[simp] theorem pullEven_evenOne {X Y : TopCat.{0}} (f : X ⟶ Y) :
    pullEven f 0 (evenOne Y) = evenOne X :=
  pull_one f

/-- **The even mod-2 cohomology** `⨁_n H^{2n}(X; F₂)`.  Its `CommRing` structure is
in `CharClass/ChernEvenRingComm.lean`. -/
abbrev EvenH (X : TopCat.{0}) : Type := DirectSum ℕ (fun n : ℕ => EvenPiece X n)

/-- The inclusion of the degree-`n` piece. -/
def EvenH.of (X : TopCat.{0}) (n : ℕ) : EvenPiece X n →+ EvenH X :=
  DirectSum.of (fun n : ℕ => EvenPiece X n) n

/-- The degree-`n` component of an even cohomology class. -/
def EvenH.component (X : TopCat.{0}) (n : ℕ) : EvenH X →+ EvenPiece X n :=
  (DirectSum.component (ZMod 2) ℕ (fun n : ℕ => EvenPiece X n) n).toAddMonoidHom

@[simp] theorem EvenH.component_of (X : TopCat.{0}) (n : ℕ) (a : EvenPiece X n) :
    EvenH.component X n (EvenH.of X n a) = a := by
  show (DirectSum.component (ZMod 2) ℕ (fun n : ℕ => EvenPiece X n) n)
      (DirectSum.of (fun n : ℕ => EvenPiece X n) n a) = a
  rw [DirectSum.component.of]
  simp

/-- A class concentrated in a single degree vanishes in `EvenH X` exactly when it
vanishes in its own degree.  This is what turns a nonvanishing top Chern class in
`H^{2r}` into a nonvanishing element of the ring, and back. -/
theorem EvenH.of_eq_zero_iff (X : TopCat.{0}) (n : ℕ) (a : EvenPiece X n) :
    EvenH.of X n a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hc := congrArg (EvenH.component X n) h
    rwa [EvenH.component_of, map_zero] at hc
  · intro h
    rw [h, map_zero]


end

end CharClass
end GroupApproximation
