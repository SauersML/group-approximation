import GroupApproximation.CharClass.ChernTotalRing
import GroupApproximation.CharClass.ChernRelation
import GroupApproximation.CharClass.LerayHirschAlgebra

/-!
# Mod-2 Chern classes of a projective bundle

Grothendieck's definition, over the mod-2 cohomology ring
`TotalH X = ⨁_n H^n(X;F₂)` of `CharClass/ChernTotalRing.lean`.  A **Leray–Hirsch
presentation** of a projective bundle `π : P → X` with fibre `ℂP^{r-1}` says that

```text
1, ξ, …, ξ^{r-1}      (ξ = e(taut) ∈ H^2(P; F₂))
```

is a basis of `H^*(P;F₂)` over `H^*(X;F₂)`.  Packaged over those rings that is a
`Mathlib` `PowerBasis (TotalH X) (TotalH P)` of dimension `r`, and the mod-2
Chern classes are by *definition* the coefficients of its `minpolyGen` — the
unique monic relation

```text
ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0.
```

Everything the classes satisfy that does not mention the topology is inherited
from `CharClass/ChernRelation.lean`: `γ_0 = 1`, vanishing above the rank,
naturality under a base change preserving the relation, the split form
`γ_k = e_k(y_1, …, y_r)`, and the Whitney sum formula along an injective base
change.

This file is the *ring* view.  The degreewise view, `CharClass/LerayHirschDegree.lean`,
reads the same classes off the Leray–Hirsch coefficients of `ξ^r` and keeps their
degrees, `γ_k ∈ H^{2k}(X;F₂)`, which the ring forgets.  Both are wanted: the ring
is where Whitney is a product of polynomials, the degreewise view is where
`γ_r ≠ 0` can be compared with a Thom class.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-- The Leray–Hirsch combination `c ↦ ∑_{i<r} π^*(c i) · ξ^i`, written with the
ring multiplication rather than a scalar action, so that its type does not mention
the algebra instance.  It *is* the scalar combination definitionally, because the
algebra map of `RingHom.toAlgebra` acts by multiplication. -/
def lhFun (π : P ⟶ X) (r : ℕ) (ξ : Hmod2 P 2) (c : Fin r → TotalH X) : TotalH P :=
  ∑ i : Fin r, TotalH.map π (c i) * TotalH.of P 2 ξ ^ (i : ℕ)

/-- **Leray–Hirsch data** for a rank-`r` projective bundle: the projection, the
tautological degree-2 class, and the statement that its powers form a basis. -/
structure LerayHirschData (X P : TopCat.{0}) where
  /-- The bundle projection. -/
  proj : P ⟶ X
  /-- The rank; the fibre is `ℂP^{rank-1}`. -/
  rank : ℕ
  /-- The Euler class of the tautological line, in degree 2. -/
  taut : Hmod2 P 2
  /-- **Leray–Hirsch**: `1, ξ, …, ξ^{rank-1}` is a basis of `TotalH P` over `TotalH X`. -/
  free : Function.Bijective (lhFun proj rank taut)

namespace LerayHirschData

variable (D : LerayHirschData X P)

/-- The `TotalH X`-algebra structure on `TotalH P` induced by the projection.
`@[reducible]` because its result is a class and every use below supplies it as an
explicit instance argument. -/
@[reducible] def algebra : Algebra (TotalH X) (TotalH P) :=
  (TotalH.map D.proj).toAlgebra

/-- The `PowerBasis` presented by Leray–Hirsch data: the input of
`CharClass/ChernRelation.lean`. -/
def powerBasis : @PowerBasis (TotalH X) (TotalH P) _ _ D.algebra :=
  @powerBasisOfBijective' (TotalH X) (TotalH P) _ _ D.algebra
    (TotalH.of P 2 D.taut) D.rank (by exact D.free)

@[simp] theorem powerBasis_dim :
    @PowerBasis.dim (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis = D.rank := rfl

@[simp] theorem powerBasis_gen :
    @PowerBasis.gen (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis
      = TotalH.of P 2 D.taut := rfl

/-- The **mod-2 Chern classes** of the bundle: the coefficients of the unique
monic degree-`rank` relation satisfied by the tautological class. -/
def chern (i : ℕ) : TotalH X :=
  @chernClass (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis i

/-- The **total Chern polynomial** `X^r + γ_1 X^{r-1} + ⋯ + γ_r`. -/
def chernPolynomial : Polynomial (TotalH X) :=
  @chernPoly (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis

theorem chernPolynomial_monic : D.chernPolynomial.Monic :=
  @chernPoly_monic (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis

/-- **The defining relation** `ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0`. -/
theorem aeval_taut_chernPolynomial :
    @Polynomial.aeval (TotalH X) (TotalH P) _ _ D.algebra
      (TotalH.of P 2 D.taut) D.chernPolynomial = 0 :=
  @aeval_gen_chernPoly (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis

/-- `γ_0 = 1`. -/
theorem chern_zero [Nontrivial (TotalH X)] : D.chern 0 = 1 :=
  @chernClass_zero (TotalH X) (TotalH P) _ _ D.algebra _ D.powerBasis

/-- `γ_i = 0` above the rank. -/
theorem chern_eq_zero_of_lt {i : ℕ} (hi : D.rank < i) : D.chern i = 0 :=
  @chernClass_eq_zero_of_lt (TotalH X) (TotalH P) _ _ D.algebra D.powerBasis i hi

end LerayHirschData

end

end CharClass
end GroupApproximation
