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

This file is downstream of graded commutativity of the cup product
(`cup_comm`, needed for `EvenH X` to be a `CommRing`); see this lane's report.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

/-- The `EvenH X`-algebra structure on `EvenH P` induced by `π : P ⟶ X`.  It is a
`def` and not an instance because it depends on the map. -/
def evenAlgebra {X P : TopCat.{0}} (π : P ⟶ X) : Algebra (EvenH X) (EvenH P) :=
  (EvenH.map π).toAlgebra

/-- The Leray–Hirsch combination `c ↦ ∑_{i<r} π^*(c i) · ξ^i`, written without a
scalar action so that its type does not mention the non-canonical `Algebra`
instance.  It is *definitionally* the scalar combination, because the algebra map
of `RingHom.toAlgebra` acts by multiplication. -/
def lhFun {X P : TopCat.{0}} (π : P ⟶ X) (r : ℕ) (ξ : EvenPiece P 1)
    (c : Fin r → EvenH X) : EvenH P :=
  ∑ i : Fin r, EvenH.map π (c i) * EvenH.of P 1 ξ ^ (i : ℕ)

/-- **Leray–Hirsch data** for a rank-`r` projective bundle over `X`: the
projection, the tautological degree-2 class, the statement that its powers form a
basis, and the grading of that basis. -/
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

namespace LerayHirschData

variable {X P : TopCat.{0}} (D : LerayHirschData X P)

/-- The `PowerBasis` presented by Leray–Hirsch data.  This is the input of
`CharClass/ChernRelation.lean`. -/
def powerBasis : @PowerBasis (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj) :=
  @powerBasisOfBijective' (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj)
    (EvenH.of P 1 D.taut) D.rank (by exact D.free)

/-- The **mod-2 Chern classes** of the bundle, as elements of the even cohomology
ring of the base: the coefficients of the unique monic degree-`rank` relation
satisfied by the tautological class. -/
def chern (i : ℕ) : EvenH X :=
  @chernClass (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj) D.powerBasis i

/-- The **total Chern polynomial** `X^r + γ_1 X^{r-1} + ⋯ + γ_r`. -/
def chernPolynomial : Polynomial (EvenH X) :=
  @chernPoly (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj) D.powerBasis

/-- `γ_0 = 1`. -/
theorem chern_zero [Nontrivial (EvenH X)] : D.chern 0 = 1 :=
  @chernClass_zero (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj) _ D.powerBasis

/-- `γ_i = 0` above the rank. -/
theorem chern_eq_zero_of_lt {i : ℕ} (hi : D.rank < i) : D.chern i = 0 :=
  @chernClass_eq_zero_of_lt (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj) D.powerBasis i
    (by simpa using hi)

/-- **The defining relation** `ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0`. -/
theorem aeval_taut_chernPolynomial :
    @Polynomial.aeval (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj)
      (EvenH.of P 1 D.taut) D.chernPolynomial = 0 :=
  @aeval_gen_chernPoly (EvenH X) (EvenH P) _ _ (evenAlgebra D.proj) D.powerBasis

end LerayHirschData

end

end CharClass
end GroupApproximation
