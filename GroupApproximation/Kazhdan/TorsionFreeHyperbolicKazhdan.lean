import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Algebra.HyperbolicInteger
import GroupApproximation.Kazhdan.ShalomFinitePresentation
import GroupApproximation.Kazhdan.IntegerNotKazhdan

/-!
# A torsion-free hyperbolic group with property `(T)` exists

This module proves, unconditionally --- no hypothesis binder, no placeholder
proof, no hand-declared postulate, no literature input --- the statement

> there is a group that is torsion-free, hyperbolic, and has Kazhdan's
> property `(T)`.

`exists_torsionFree_hyperbolic_kazhdan` is that statement, with
`IsPowerTorsionFree` from `Algebra/GroupTorsionFree.lean`,
`Hyperbolic.IsHyperbolicGroup` from `Algebra/HyperbolicGroup.lean`, and
`HasKazhdanPropertyT` from `Kazhdan/Kazhdan.lean`.

## The witness is the trivial group, and that is not an accident

The proof takes the trivial group.  It is torsion-free, it is `0`-hyperbolic on
the empty alphabet, and it has property `(T)` with the empty Kazhdan set.

That is the whole of what the literal statement asks for, and it is worth being
blunt about the consequence: **the literal statement is degenerate.**  A finite
group is hyperbolic (`Hyperbolic.isHyperbolicGroup_of_finite`: its word metric
with respect to the whole group is bounded by one) and has property `(T)`, and a
torsion-free finite group is trivial (`subsingleton_of_finite_of_isPowerTorsionFree`,
whence `subsingleton_of_finite`: *every* finite witness of the three clauses is
the trivial group), so the finite part of the statement collapses to a single
point.  Any unconditional proof that terminates here has proved exactly this and
nothing more.

## The statement that carries the mathematics

`SharpExistence` below is the assertion the literature actually makes and the
one that consumers want: the same three clauses **for an infinite finitely
presented group**.  It is *not* proved here, and it is not proved anywhere in
this repository or in Mathlib.  The two known routes are

* a torsion-free cocompact lattice in `Sp(n,1)`, `n ≥ 2` --- hyperbolic because
  the lattice is quasi-isometric to a negatively curved symmetric space,
  Kazhdan by Kostant's theorem that `Sp(n,1)` has property `(T)`, and
  torsion-free after passing to a finite-index subgroup by Selberg's lemma; and
* a random group at density `1/3 < d < 1/2`, which is torsion-free and
  hyperbolic (Gromov; Ollivier, *A January 2005 invitation to random groups*)
  and Kazhdan by Zuk's theorem, as used by Ollivier--Wise.

Both are far outside what is formalized here, and `SharpExistence` is recorded
as a `Prop`-valued definition precisely so that it can be *stated* without being
assumed: nothing in this repository consumes it, and no theorem below is
conditional on it.

## Where the difficulty sits

It is not in torsion-freeness, and not in hyperbolicity, and not in being
infinite.  `Algebra/HyperbolicInteger.lean` computes the word metric of the
infinite cyclic group and checks the four-point condition at `δ = 0`, so
`exists_infinite_torsionFree_hyperbolic_not_kazhdan` below produces an infinite
torsion-free hyperbolic group with two lines of proof --- and that group fails
property `(T)`, by `not_hasKazhdanPropertyT_multiplicative_int`.  Property `(T)`
is the entire content of `SharpExistence`.

## What this module deliberately does not do

`Sofic/SmallCancellationKazhdanEnvelope.lean` records the Fournier-Facio route's
input as `HyperbolicKazhdanPartner`.  Until `Algebra/HyperbolicGroup.lean` landed
its stated fields were finite presentation, torsion-freeness and property `(T)`
--- hyperbolicity was not among them, because the library could not state it ---
and *every one of those fields holds of the trivial group*, so `trivialWitness`
would have inhabited it and the route's rows would have read as discharged by a
witness that discharges nothing.

That hole is now closed from the other side: the structure carries hyperbolicity
and infiniteness as fields, and `trivialWitness_not_infinite` is exactly the
obstruction that stops this module's witness from satisfying it.  No instance of
`HyperbolicKazhdanPartner` is declared here or anywhere, and rows `KC.21` and
`LI.12b` are unaffected by this module.
-/

namespace GroupApproximation
namespace Hyperbolic

/-! ## The bundled statement -/

/-- **A torsion-free hyperbolic Kazhdan group**, bundled: the three clauses of
the statement, carried with the group they are about. -/
structure TorsionFreeHyperbolicKazhdanGroup where
  /-- The underlying group. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  /-- The group is torsion-free. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- Some finite symmetric generating set satisfies Gromov's four-point
  condition. -/
  hyperbolic : IsHyperbolicGroup Carrier
  /-- The group has Kazhdan's property `(T)`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier

instance torsionFreeHyperbolicKazhdanGroupGroup (H : TorsionFreeHyperbolicKazhdanGroup) :
    Group H.Carrier :=
  H.groupCarrier

/-! ## The witness -/

/-- **The trivial group, as a torsion-free hyperbolic Kazhdan group.**  The free
group on the empty alphabet is trivial (`Shalom.freeGroup_subsingleton_of_isEmpty`),
hence torsion-free; `isHyperbolicGroup_of_subsingleton` gives hyperbolicity at
`δ = 0` on the empty generating set, and `Shalom.hasKazhdanPropertyT_of_subsingleton`
gives property `(T)` with the empty Kazhdan set. -/
def trivialWitness : TorsionFreeHyperbolicKazhdanGroup where
  Carrier := FreeGroup Empty
  torsionFree := by
    haveI := Shalom.freeGroup_subsingleton_of_isEmpty (α := Empty)
    intro g n _ _
    exact Subsingleton.elim g 1
  hyperbolic := by
    haveI := Shalom.freeGroup_subsingleton_of_isEmpty (α := Empty)
    exact isHyperbolicGroup_of_subsingleton
  kazhdan := by
    haveI := Shalom.freeGroup_subsingleton_of_isEmpty (α := Empty)
    exact Shalom.hasKazhdanPropertyT_of_subsingleton

/-- **A torsion-free hyperbolic group with property `(T)` exists.**

Unconditional, and degenerate: the witness is the trivial group, and the module
docstring explains why no unconditional argument in this repository reaches an
infinite one.  `SharpExistence` is the statement that does not degenerate. -/
theorem exists_torsionFree_hyperbolic_kazhdan :
    ∃ (G : Type) (_ : Group G),
      IsPowerTorsionFree G ∧ IsHyperbolicGroup G ∧ HasKazhdanPropertyT.{0, 0} G :=
  ⟨trivialWitness.Carrier, trivialWitness.groupCarrier, trivialWitness.torsionFree,
    trivialWitness.hyperbolic, trivialWitness.kazhdan⟩

/-- The witness is finite --- stated so that the gap between
`exists_torsionFree_hyperbolic_kazhdan` and `SharpExistence` is machine-checked
rather than asserted in prose. -/
theorem trivialWitness_not_infinite : ¬ Infinite trivialWitness.Carrier := by
  have hsub : Subsingleton trivialWitness.Carrier :=
    Shalom.freeGroup_subsingleton_of_isEmpty (α := Empty)
  intro h
  exact h.not_finite (@Finite.of_subsingleton _ hsub)

/-- **A finite torsion-free group is trivial.**  Every element of a finite group
has finite order, and torsion-freeness kills every element of finite order. -/
theorem subsingleton_of_finite_of_isPowerTorsionFree {G : Type*} [Group G] [Finite G]
    (h : IsPowerTorsionFree G) : Subsingleton G := by
  have key : ∀ g : G, g = 1 := by
    intro g
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite g)
    exact h g n hn hpow
  constructor
  intro a b
  rw [key a, key b]

/-- **Every finite witness is the trivial group.**  This is the exact sense in
which the literal statement degenerates: hyperbolicity and property `(T)` are
automatic for finite groups, so the finite part of the search space is a single
point, and reaching anything else means reaching an infinite group. -/
theorem subsingleton_of_finite (H : TorsionFreeHyperbolicKazhdanGroup) [Finite H.Carrier] :
    Subsingleton H.Carrier :=
  subsingleton_of_finite_of_isPowerTorsionFree H.torsionFree

/-! ## The sharp statement, stated and not assumed -/

/-- **The statement the literature makes.**  An *infinite*, finitely presented,
torsion-free hyperbolic group with property `(T)`.

This is a definition, not a theorem and not an axiom: nothing below proves it,
nothing in this repository assumes it, and no declaration is conditional on it.
It is recorded so that the distance between the degenerate
`exists_torsionFree_hyperbolic_kazhdan` and the intended statement is a named
object rather than a remark. -/
def SharpExistence : Prop :=
  ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.IsFinitelyPresented G ∧ IsPowerTorsionFree G ∧
      IsHyperbolicGroup G ∧ HasKazhdanPropertyT.{0, 0} G

/-! ## Locating the difficulty -/

/-- **Every clause of `SharpExistence` but property `(T)` comes for free.**  The
infinite cyclic group is infinite, torsion-free and `0`-hyperbolic --- and it
fails property `(T)`.  So none of the other clauses, in any combination, forces
`(T)`: the sharp statement is a statement about `(T)`. -/
theorem exists_infinite_torsionFree_hyperbolic_not_kazhdan :
    ∃ (G : Type) (_ : Group G),
      Infinite G ∧ IsPowerTorsionFree G ∧ IsHyperbolicGroup G ∧
        ¬ HasKazhdanPropertyT.{0, 0} G :=
  ⟨Multiplicative ℤ, inferInstance, infinite_multiplicative_int,
    isPowerTorsionFree_multiplicative_int, isHyperbolicGroup_multiplicative_int,
    not_hasKazhdanPropertyT_multiplicative_int⟩

end Hyperbolic
end GroupApproximation
