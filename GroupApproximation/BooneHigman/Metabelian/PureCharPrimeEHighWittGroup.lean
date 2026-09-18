import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCarry
import Mathlib.Algebra.Group.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# An explicit model of the additive group `W₂(L)` (bh-met-87c, part 2)

`eHighWitt_W2 L p` is `L × L` with the length-two Witt addition
`(x₀, x₁) + (y₀, y₁) = (x₀ + y₀, x₁ + y₁ - carry p x₀ y₀)`, zero `(0, 0)`, and negation
`-(x₀, x₁) = (-x₀, -x₁ + carry p (-x₀) x₀)`.  The carry is `eHighWitt_carry`
(`PureCharPrimeEHighWittCarry`).

The additive group laws hold over any commutative ring `L`.  They follow from the carry cocycle
identities, which are proved universally in `ℤ[X₀, X₁, X₂]` and transported here along
`eval₂Hom`.  The second coordinate of the sum is exactly the Witt addition polynomial
`S₁ = X₁ + Y₁ + (X₀^p + Y₀^p - (X₀ + Y₀)^p) / p`, so for a perfect field `L` of characteristic
`p` this group is the usual `W₂(L)`.  No statement here depends on that identification: the
model is used only as an explicit target group.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

section Transfer

variable {R : Type*} [CommRing R] {p : ℕ}

/-- Commutativity of the carry, in every commutative ring. -/
theorem eHighWitt_carry_comm (hp : p.Prime) (a b : R) :
    eHighWitt_carry p a b = eHighWitt_carry p b a := by
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b, 0])
    (eHighWitt_carry_comm_univ hp)
  simp only [eHighWitt_carry_map, MvPolynomial.eval₂Hom_X'] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_comm

/-- `carry a 0 = 0`, in every commutative ring. -/
theorem eHighWitt_carry_zero_right (hp : p.Prime) (a : R) : eHighWitt_carry p a 0 = 0 := by
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, a, a])
    (eHighWitt_carry_zero_right_univ hp)
  simp only [eHighWitt_carry_map, map_zero, MvPolynomial.eval₂Hom_X'] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_zero_right

/-- `carry 0 b = 0`, in every commutative ring. -/
theorem eHighWitt_carry_zero_left (hp : p.Prime) (b : R) : eHighWitt_carry p 0 b = 0 := by
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![b, b, b])
    (eHighWitt_carry_zero_left_univ hp)
  simp only [eHighWitt_carry_map, map_zero, MvPolynomial.eval₂Hom_X'] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_zero_left

/-- The carry cocycle identity, in every commutative ring. -/
theorem eHighWitt_carry_assoc (hp : p.Prime) (a b e : R) :
    eHighWitt_carry p a b + eHighWitt_carry p (a + b) e =
      eHighWitt_carry p b e + eHighWitt_carry p a (b + e) := by
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b, e])
    (eHighWitt_carry_assoc_univ hp)
  simp only [eHighWitt_carry_map, map_add, MvPolynomial.eval₂Hom_X'] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_carry_assoc

end Transfer

/-- The explicit model of `W₂(L)`, as a pair of coordinates `(x0, x1)`. -/
@[ext]
structure eHighWitt_W2 (L : Type) (p : ℕ) where
  /-- The zeroth Witt coordinate. -/
  x0 : L
  /-- The first Witt coordinate. -/
  x1 : L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2

section Group

variable {L : Type} [CommRing L] {p : ℕ}

instance eHighWitt_W2.instAdd : Add (eHighWitt_W2 L p) :=
  ⟨fun x y => ⟨x.x0 + y.x0, x.x1 + y.x1 - eHighWitt_carry p x.x0 y.x0⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2.instAdd

instance eHighWitt_W2.instZero : Zero (eHighWitt_W2 L p) := ⟨⟨0, 0⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2.instZero

instance eHighWitt_W2.instNeg : Neg (eHighWitt_W2 L p) :=
  ⟨fun x => ⟨-x.x0, -x.x1 + eHighWitt_carry p (-x.x0) x.x0⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2.instNeg

theorem eHighWitt_W2_add_x0 (x y : eHighWitt_W2 L p) : (x + y).x0 = x.x0 + y.x0 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_add_x0

theorem eHighWitt_W2_add_x1 (x y : eHighWitt_W2 L p) :
    (x + y).x1 = x.x1 + y.x1 - eHighWitt_carry p x.x0 y.x0 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_add_x1

theorem eHighWitt_W2_zero_x0 : (0 : eHighWitt_W2 L p).x0 = 0 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_zero_x0

theorem eHighWitt_W2_zero_x1 : (0 : eHighWitt_W2 L p).x1 = 0 := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_zero_x1

theorem eHighWitt_W2_add_assoc (hp : p.Prime) (x y z : eHighWitt_W2 L p) :
    x + y + z = x + (y + z) := by
  refine eHighWitt_W2.ext ?_ ?_
  · show x.x0 + y.x0 + z.x0 = x.x0 + (y.x0 + z.x0)
    ring
  · show x.x1 + y.x1 - eHighWitt_carry p x.x0 y.x0 + z.x1 -
        eHighWitt_carry p (x.x0 + y.x0) z.x0 =
      x.x1 + (y.x1 + z.x1 - eHighWitt_carry p y.x0 z.x0) -
        eHighWitt_carry p x.x0 (y.x0 + z.x0)
    linear_combination (-1 : L) * eHighWitt_carry_assoc hp x.x0 y.x0 z.x0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_add_assoc

theorem eHighWitt_W2_zero_add (hp : p.Prime) (x : eHighWitt_W2 L p) : 0 + x = x := by
  refine eHighWitt_W2.ext ?_ ?_
  · show 0 + x.x0 = x.x0
    ring
  · show 0 + x.x1 - eHighWitt_carry p 0 x.x0 = x.x1
    rw [eHighWitt_carry_zero_left hp]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_zero_add

theorem eHighWitt_W2_add_zero (hp : p.Prime) (x : eHighWitt_W2 L p) : x + 0 = x := by
  refine eHighWitt_W2.ext ?_ ?_
  · show x.x0 + 0 = x.x0
    ring
  · show x.x1 + 0 - eHighWitt_carry p x.x0 0 = x.x1
    rw [eHighWitt_carry_zero_right hp]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_add_zero

theorem eHighWitt_W2_neg_add_cancel (x : eHighWitt_W2 L p) : -x + x = 0 := by
  refine eHighWitt_W2.ext ?_ ?_
  · show -x.x0 + x.x0 = 0
    ring
  · show -x.x1 + eHighWitt_carry p (-x.x0) x.x0 + x.x1 - eHighWitt_carry p (-x.x0) x.x0 = 0
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_neg_add_cancel

theorem eHighWitt_W2_add_comm (hp : p.Prime) (x y : eHighWitt_W2 L p) : x + y = y + x := by
  refine eHighWitt_W2.ext ?_ ?_
  · show x.x0 + y.x0 = y.x0 + x.x0
    ring
  · show x.x1 + y.x1 - eHighWitt_carry p x.x0 y.x0 = y.x1 + x.x1 - eHighWitt_carry p y.x0 x.x0
    rw [eHighWitt_carry_comm hp x.x0 y.x0]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2_add_comm

/-- The additive group `W₂(L)` for a prime `p`. -/
instance eHighWitt_W2.instAddCommGroup [Fact p.Prime] : AddCommGroup (eHighWitt_W2 L p) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc := eHighWitt_W2_add_assoc Fact.out
  zero_add := eHighWitt_W2_zero_add Fact.out
  add_zero := eHighWitt_W2_add_zero Fact.out
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := eHighWitt_W2_neg_add_cancel
  add_comm := eHighWitt_W2_add_comm Fact.out

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWitt_W2.instAddCommGroup

end Group

end GroupApproximation.BooneHigman.Metabelian.Coprimary
