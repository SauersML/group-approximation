import GroupApproximation.CharClass.ChernEvenRingComm
import GroupApproximation.CharClass.ChernRelation
import GroupApproximation.CharClass.LerayHirschAlgebra

/-!
# Mod-2 Chern classes of a projective bundle

This is where the algebra of `CharClass/ChernRelation.lean` meets the ring of
`CharClass/ChernEvenRingComm.lean`.  A **Leray–Hirsch presentation** of a
projective bundle `π : P → X` with fibre `ℂP^{r-1}` says that

```text
1, ξ, …, ξ^{r-1}      (ξ = e(taut) ∈ H^2(P; F₂))
```

is a basis of `H^*(P;F₂)` over `H^*(X;F₂)`.  Packaged over the even cohomology
rings that is a `Mathlib` `PowerBasis (EvenH X) (EvenH P)` of dimension `r`, and
the mod-2 Chern classes `γ_i(E)` are then, by *definition*, the coefficients of
its `minpolyGen` — the unique monic relation

```text
ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0.
```

Everything the classes satisfy that does not mention the topology — the
normalisation `γ_0 = 1`, vanishing above the rank, naturality, the split form
`γ_k = e_k(y_1, …, y_r)`, and the Whitney sum formula along an injective base
change — is already proved in `ChernRelation.lean` and is inherited here.

## The one field that is not proved here

`LerayHirschData.coeff_homogeneous` records that the Leray–Hirsch isomorphism is
**graded**: the coefficient of `ξ^i` in a class of degree `n` sits in degree
`n - i`.  It is a field of the structure rather than a theorem because it is
discharged by the *degreewise* Leray–Hirsch statement — the Mayer–Vietoris
induction over a finite trivializing cover proves bijectivity in each degree
separately, and the total bijectivity plus the grading are two shadows of that
one statement.  It is what makes `γ_i(E)` live in `H^{2i}(X;F₂)` rather than
merely in the total ring, which is what lane `cc-thom` needs in order to compare
`γ_r` with a Thom class in `H^{2r}`.

## What is here, and what waits

**Here:** the Leray–Hirsch combination `lhFun` and the structure `LerayHirschData`
packaging a Leray–Hirsch presentation.  Neither needs any commutativity: `lhFun`
uses only the ring structure of `EvenH P`, which `evenGRing` supplies
unconditionally, so peers can build against this interface today.

**Deferred to the full-graded-ring migration:** the `PowerBasis`, and with it
`γ_i` as an element of `EvenH X`.  The obstruction is not mathematical but an
instance diamond, and it is worth stating exactly, because it decides the shape
of that migration.

## Why the `PowerBasis` cannot be stated yet

`Algebra (EvenH X) (EvenH P)` cannot be *built* here: `RingHom.toAlgebra` wants a
`CommSemiring` target and `RingHom.toAlgebra'` wants the image of `EvenH.map π`
to be central, and both are graded commutativity of the cup product, which waits
on `cc-steenrod`'s `cup_comm`.

Taking it as an ambient instance variable does not help either, and the reason is
worth recording.  `EvenH X` acquires a `Semiring` by **two** routes:
`DirectSum.semiring`, because `evenGRing` is an instance, and
`CommRing.toCommSemiring.toSemiring`, from any commutativity hypothesis.  The two
are definitionally equal but not syntactically so, and every type that mentions
the ring structure — `Polynomial (EvenH X)`, the `1` of `γ₀ = 1`, the `0` of the
rank bound — pins one of them at elaboration time.  A statement written here
picks `DirectSum.semiring`; a lemma imported from `ChernRelation.lean`, whose
section variable is `[CommRing A]`, produces the other.  Nothing local fixes
this: it has to be settled by having a single route to the ring structure, which
is precisely what the migration to the full graded ring `⨁_n H^n(X;F₂)` will do,
since there the multiplication is `cup` with no degree transport and the graded
structure is the only source of the ring.

Until then the classes come from `CharClass/LerayHirschDegree.lean`, which
defines them degreewise straight off the Leray–Hirsch coefficients of `ξ^r`, with
`γ_k ∈ H^{2k}(X;F₂)` correct by construction and no ring anywhere.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

/-- The Leray–Hirsch combination `c ↦ ∑_{i<r} π^*(c i) · ξ^i`, written without a
scalar action so that its type does not mention the non-canonical `Algebra`
instance.  It is *definitionally* the scalar combination, because the algebra map
of `RingHom.toAlgebra` acts by multiplication. -/
def lhFun {X P : TopCat.{0}} (π : P ⟶ X) (r : ℕ) (ξ : EvenPiece P 1)
    (c : Fin r → EvenH X) : EvenH P :=
  ∑ i : Fin r, EvenH.map π (c i) * EvenH.of P 1 ξ ^ (i : ℕ)

/-- **Leray–Hirsch data** for a rank-`r` projective bundle over `X`: the
projection, the tautological degree-2 class, the statement that its powers form a
basis, and the grading of that basis.

No commutativity is needed anywhere in this structure: `lhFun` uses only the ring
structure of `EvenH P`, which `evenGRing` supplies unconditionally. -/
structure LerayHirschData (X P : TopCat.{0}) where
  /-- The bundle projection. -/
  proj : P ⟶ X
  /-- The rank of the vector bundle, i.e. the fibre is `ℂP^{rank-1}`. -/
  rank : ℕ
  /-- The Euler class of the tautological line on `P`, in degree 2. -/
  taut : EvenPiece P 1
  /-- **Leray–Hirsch**: `1, ξ, …, ξ^{rank-1}` is a basis of `EvenH P` over `EvenH X`. -/
  free : Function.Bijective (lhFun proj rank taut)
  /-- **The basis is graded**: the coefficient of `ξ^i` in a homogeneous class of
  degree `n` is homogeneous of degree `n - i`.  Discharged by the degreewise form
  of Leray–Hirsch, which is what the Mayer–Vietoris induction over a finite
  trivializing cover of the base actually proves; the field records it separately
  because `EvenH` forgets the grading. -/
  coeff_homogeneous : ∀ (n : ℕ) (c : Fin rank → EvenH X) (z : EvenPiece P n),
      lhFun proj rank taut c = EvenH.of P n z →
      ∀ i : Fin rank, ∃ a : EvenPiece X (n - i), c i = EvenH.of X (n - i) a

end

end CharClass
end GroupApproximation
