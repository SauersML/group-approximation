import GroupApproximation.CharClass.CupOneTotal
import GroupApproximation.Meta.AxiomGuard

/-!
# The even part of the cohomology ring over `K`, as a commutative ring

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4–1.5; lead's ruling of 2026-09-11 assigning
the concrete mod-`p` assembly of Step D to this lane).

`CharClass/ParityPData.lean` states Step D mod `p` over a pair of **commutative** rings: `R`
is `H^*(Y; F_p)` and `H` is the even part of `H^*(N; F_p)`.  Over a general coefficient ring
`K` the whole cohomology ring `TotalHOf K X` (`CharClass/ChernTotalRingOf.lean`) is only a
graded ring, and at odd `p` it is genuinely not commutative.  What is commutative is its
even part: `lix-cupone`'s `TotalHOf.mul_comm_of_isEven_left` (`CharClass/CupOneTotal.lean`)
says an even class commutes with every element.  This file turns that into the commutative
ring the even side consumes:

* `Gen.evenPart K X` — the subring of classes vanishing in every odd degree;
* `Gen.instCommRingEvenPart` — **it is a commutative ring**, with no hypothesis on `K` or `X`;
* `Gen.evenMap K f` — pullback, restricted to the even parts, as a ring homomorphism;
* `Gen.evenRestrictAdd f hf` — an additive operation preserving evenness (the reduced powers),
  restricted to the even part.

Nothing is re-derived: closure under the ring operations and pullback is `lix-cupone`'s
`IsEven.add/mul/map`, `isEven_zero/one`, and commutativity is `mul_comm_of_isEven_left`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gen

open CategoryTheory

noncomputable section

/-- **The even part of `H^*(X; K)`**: the classes vanishing in every odd degree. -/
def evenPart (K : Type) [CommRing K] (X : TopCat.{0}) : Subring (TotalHOf K X) where
  carrier := {x | TotalHOf.IsEven x}
  mul_mem' {a b} ha hb := TotalHOf.IsEven.mul ha hb
  one_mem' := TotalHOf.isEven_one K X
  add_mem' {a b} ha hb := TotalHOf.IsEven.add ha hb
  zero_mem' := TotalHOf.isEven_zero K X
  neg_mem' {x} hx := by
    show TotalHOf.IsEven (-x)
    have hx' : TotalHOf.IsEven x := hx
    intro n hn
    rw [map_neg, hx' n hn, neg_zero]

theorem mem_evenPart {K : Type} [CommRing K] {X : TopCat.{0}} {x : TotalHOf K X} :
    x ∈ evenPart K X ↔ TotalHOf.IsEven x :=
  Iff.rfl

/-- **The even part is a commutative ring**, over every commutative coefficient ring: an even
class commutes with every class (`TotalHOf.mul_comm_of_isEven_left`). -/
instance instCommRingEvenPart (K : Type) [CommRing K] (X : TopCat.{0}) :
    CommRing (evenPart K X) :=
  { (evenPart K X).toRing with
    mul_comm := fun a b =>
      Subtype.ext (TotalHOf.mul_comm_of_isEven_left (mem_evenPart.mp a.2) (b : TotalHOf K X)) }

/-- **Pullback on the even parts**, as a ring homomorphism. -/
def evenMap (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    evenPart K Y →+* evenPart K X where
  toFun a := ⟨TotalHOf.map K f a, TotalHOf.IsEven.map f (mem_evenPart.mp a.2)⟩
  map_one' := Subtype.ext (map_one (TotalHOf.map K f))
  map_mul' a b := Subtype.ext (map_mul (TotalHOf.map K f) a b)
  map_zero' := Subtype.ext (map_zero (TotalHOf.map K f))
  map_add' a b := Subtype.ext (map_add (TotalHOf.map K f) a b)

@[simp] theorem coe_evenMap (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (a : evenPart K Y) : (evenMap K f a : TotalHOf K X) = TotalHOf.map K f a :=
  rfl

/-- **An additive operation preserving evenness, restricted to the even part.**  The reduced
powers `P^i` are the intended instance. -/
def evenRestrictAdd {K : Type} [CommRing K] {X : TopCat.{0}} (f : TotalHOf K X →+ TotalHOf K X)
    (hf : ∀ x : TotalHOf K X, TotalHOf.IsEven x → TotalHOf.IsEven (f x)) :
    evenPart K X →+ evenPart K X where
  toFun a := ⟨f a, hf a (mem_evenPart.mp a.2)⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f a b)

@[simp] theorem coe_evenRestrictAdd {K : Type} [CommRing K] {X : TopCat.{0}}
    (f : TotalHOf K X →+ TotalHOf K X)
    (hf : ∀ x : TotalHOf K X, TotalHOf.IsEven x → TotalHOf.IsEven (f x)) (a : evenPart K X) :
    (evenRestrictAdd f hf a : TotalHOf K X) = f a :=
  rfl

end

#audit_axioms evenPart
#audit_axioms mem_evenPart
#audit_axioms instCommRingEvenPart
#audit_axioms evenMap
#audit_axioms evenRestrictAdd

end Gen
end CharClass
end GroupApproximation
