import GroupApproximation.CharClass.ChernEvenRing

/-!
# The even mod-2 cohomology ring is commutative

The last field of the graded ring structure on `⨁_n H^{2n}(X; F₂)`, and the only
one that is a genuine theorem about the Alexander–Whitney product rather than
bookkeeping: mod 2 the cup product is graded commutative, which for even degrees
means commutative on the nose.  The proof of `cup_comm` is the `⌣₁` chain
homotopy, `δ(α ⌣₁ β) = δα ⌣₁ β + α ⌣₁ δβ + α ⌣ β + β ⌣ α`, so that `α ⌣ β + β ⌣ α`
is a coboundary whenever `α` and `β` are cocycles.  That formula belongs to lanes
`cc-steenrod` / `cc-cartan`; this file is what turns it into a `CommRing`.

With the `CommRing` in hand, `EvenH.map` makes `EvenH` a contravariant functor
into commutative rings, which is what puts `Polynomial (EvenH X)` and
`PowerBasis (EvenH X) (EvenH (P E))` — hence `CharClass/ChernRelation.lean` — in
range.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- The signature `cc-steenrod`/`cc-cartan` are to deliver for graded commutativity
of the cup product: the shape recorded in `notes/lix-lane-reports/cc-projective.md`.
Everything below is a theorem about any space equipped with such a fact — nothing
here is a `sorry` or an `axiom` — and the eventual `instance` gluing it to a real
proof of `CupComm` is one line, added once that proof exists. -/
def CupComm (X : TopCat.{0}) : Prop :=
  ∀ {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q), cup a b = cohCast (Nat.add_comm q p) (cup b a)

/-- **Commutativity of the even cup product**, transported, given `CupComm X`. -/
theorem evenMul_comm {X : TopCat.{0}} (hcc : CupComm X) {m n : ℕ}
    (a : EvenPiece X m) (b : EvenPiece X n) (h : 2 * (m + n) = 2 * (n + m)) :
    cohCast h (evenMul a b) = evenMul b a := by
  show cohCast h (cohCast (two_mul_add m n) (cup a b)) = cohCast (two_mul_add n m) (cup b a)
  rw [hcc a b, cohCast_cohCast, cohCast_cohCast]

/-- **The even mod-2 cohomology of a space is a graded commutative ring**, given
`CupComm X`.  This is a `def` and not an `instance`: `cc-steenrod` has not yet
delivered a proof of `CupComm X`, and until it does there is nothing to apply
this to.  Once it does, `instance : DirectSum.GCommRing (fun n => EvenPiece X n) :=
gCommRing X thatProof` is the whole remaining step. -/
@[reducible]
def gCommRing (X : TopCat.{0}) (hcc : CupComm X) :
    DirectSum.GCommRing (fun n : ℕ => EvenPiece X n) where
  __ := evenGRing X
  mul_comm a b := by
    obtain ⟨m, a⟩ := a
    obtain ⟨n, b⟩ := b
    have hdeg : 2 * (m + n) = 2 * (n + m) := by omega
    exact Sigma.ext (Nat.add_comm m n)
      (heq_of_evenCast hdeg (evenMul a b) (evenMul b a) (evenMul_comm hcc a b hdeg))

theorem EvenH.of_mul (X : TopCat.{0}) (m n : ℕ) (a : EvenPiece X m) (b : EvenPiece X n) :
    EvenH.of X (m + n) (evenMul a b) = EvenH.of X m a * EvenH.of X n b :=
  (DirectSum.of_mul_of a b).symm

@[simp] theorem EvenH.of_one (X : TopCat.{0}) : EvenH.of X 0 (evenOne X) = 1 := rfl

/-- **Pullback as a ring homomorphism.** -/
def EvenH.map {X Y : TopCat.{0}} (f : X ⟶ Y) : EvenH Y →+* EvenH X :=
  DirectSum.toSemiring (fun n => (EvenH.of X n).comp (pullEven f n))
    (by
      show EvenH.of X 0 (pullEven f 0 (evenOne Y)) = 1
      rw [pullEven_evenOne]
      exact EvenH.of_one X)
    (fun {m n} a b => by
      show EvenH.of X (m + n) (pullEven f (m + n) (evenMul a b))
        = EvenH.of X m (pullEven f m a) * EvenH.of X n (pullEven f n b)
      rw [pullEven_evenMul, EvenH.of_mul])

@[simp] theorem EvenH.map_of {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : EvenPiece Y n) :
    EvenH.map f (EvenH.of Y n a) = EvenH.of X n (pullEven f n a) :=
  DirectSum.toSemiring_of _ _ _ n a

end

end CharClass
end GroupApproximation
