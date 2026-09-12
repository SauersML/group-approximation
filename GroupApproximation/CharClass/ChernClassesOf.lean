import GroupApproximation.CharClass.ChernTotalRingOf
import GroupApproximation.CharClass.ChernRelation
import GroupApproximation.CharClass.LerayHirschAlgebra

/-!
# Chern classes of a projective bundle with coefficients in `K`

The coefficient-generic form of `ChernClasses`.  Over `F₂` the cohomology ring is commutative
outright; over a general `K` it is only graded-commutative, so `TotalHOf K X` is a `Ring`
(`ChernTotalRingOf.instGRingOf`) and Grothendieck's definition needs two facts that are
**hypotheses of the data**, not consequences of the ring:

* `mul_comm_base` — the base ring is commutative.  It holds whenever the cohomology of the base
  is concentrated in even degrees (a product of projective spaces), by `cup_comm_of_even_left`
  componentwise; that producer is `CupOneTotal`'s `mul_comm_of_isEven`.
* `map_central` — classes pulled back from the base are central in the total space.  It holds
  when the base classes are even, for the same reason.

With those, a Leray–Hirsch presentation `1, ξ, …, ξ^{r-1}` is a `PowerBasis` of
`TotalHOf K P` over `TotalHOf K X`, and the Chern classes are by definition the coefficients of
its `minpolyGen`,

```text
ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0.
```

**The root convention is not restated here.**  It is fixed once, in `ChernRelation`'s
`Conventions` block (`ξ = e(O(1))`, so `γ_k = e_k(y)` with the classical Chern roots `y`, no
sign); this file only packages the data that block is about.

## Main declarations

* `lhFunOf`, `LerayHirschDataOf` — the Leray–Hirsch combination and the data.
* `LerayHirschDataOf.commRing`, `LerayHirschDataOf.algebra`, `LerayHirschDataOf.powerBasis`.
* `LerayHirschDataOf.chern`, `chernPolynomial`, `chernPolynomial_monic`,
  `aeval_taut_chernPolynomial`, `chern_zero`, `chern_eq_zero_of_lt`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-- The Leray–Hirsch combination `c ↦ ∑_{i<r} π^*(c i) · ξ^i` over `K`, written with the ring
multiplication so that its type does not mention an algebra instance. -/
def lhFunOf (K : Type) [CommRing K] (π : P ⟶ X) (r : ℕ) (ξ : Hmod K P 2)
    (c : Fin r → TotalHOf K X) : TotalHOf K P :=
  ∑ i : Fin r, TotalHOf.map K π (c i) * TotalHOf.of K P 2 ξ ^ (i : ℕ)

/-- **Leray–Hirsch data over `K`** for a rank-`r` projective bundle. -/
structure LerayHirschDataOf (K : Type) [CommRing K] (X P : TopCat.{0}) where
  /-- The bundle projection. -/
  proj : P ⟶ X
  /-- The rank; the fibre is `ℂP^{rank-1}`. -/
  rank : ℕ
  /-- The Euler class of the (dual) tautological line, in degree 2. -/
  taut : Hmod K P 2
  /-- The base cohomology ring is commutative. -/
  mul_comm_base : ∀ a b : TotalHOf K X, a * b = b * a
  /-- Classes pulled back from the base are central in the total space. -/
  map_central : ∀ (c : TotalHOf K X) (x : TotalHOf K P),
    TotalHOf.map K proj c * x = x * TotalHOf.map K proj c
  /-- **Leray–Hirsch**: `1, ξ, …, ξ^{rank-1}` is a basis of `TotalHOf K P` over the base. -/
  free : Function.Bijective (lhFunOf K proj rank taut)

namespace LerayHirschDataOf

variable {K : Type} [CommRing K] (D : LerayHirschDataOf K X P)

/-- The commutative ring structure on the base, with the operations of `instGRingOf`. -/
@[reducible] def commRing : CommRing (TotalHOf K X) :=
  { (inferInstance : Ring (TotalHOf K X)) with mul_comm := D.mul_comm_base }

/-- The `TotalHOf K X`-algebra structure on `TotalHOf K P` induced by the projection; the
image is central by `map_central`. -/
@[reducible] def algebra :
    @Algebra (TotalHOf K X) (TotalHOf K P) D.commRing.toCommSemiring inferInstance :=
  @RingHom.toAlgebra' (TotalHOf K X) (TotalHOf K P) D.commRing.toCommSemiring inferInstance
    (TotalHOf.map K D.proj) D.map_central

/-- The `PowerBasis` presented by Leray–Hirsch data over `K`. -/
def powerBasis : @PowerBasis (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra :=
  @powerBasisOfBijective' (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra
    (TotalHOf.of K P 2 D.taut) D.rank (by exact D.free)

@[simp] theorem powerBasis_dim :
    @PowerBasis.dim (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra
      D.powerBasis = D.rank := rfl

@[simp] theorem powerBasis_gen :
    @PowerBasis.gen (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra
      D.powerBasis = TotalHOf.of K P 2 D.taut := rfl

/-- The **Chern classes** of the bundle over `K`: the coefficients of the unique monic
degree-`rank` relation satisfied by the tautological class. -/
def chern (i : ℕ) : TotalHOf K X :=
  @chernClass (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra D.powerBasis i

/-- The **total Chern polynomial** `X^r + γ_1 X^{r-1} + ⋯ + γ_r`. -/
def chernPolynomial :=
  @chernPoly (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra D.powerBasis

theorem chernPolynomial_monic : @Polynomial.Monic (TotalHOf K X) _ D.chernPolynomial :=
  @chernPoly_monic (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra
    D.powerBasis

/-- **The defining relation** `ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0`. -/
theorem aeval_taut_chernPolynomial :
    @Polynomial.aeval (TotalHOf K X) (TotalHOf K P) D.commRing.toCommSemiring inferInstance
      D.algebra
      (TotalHOf.of K P 2 D.taut) D.chernPolynomial = 0 :=
  @aeval_gen_chernPoly (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra
    D.powerBasis

/-- `γ_0 = 1`. -/
theorem chern_zero [Nontrivial (TotalHOf K X)] : D.chern 0 = 1 :=
  @chernClass_zero (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra _
    D.powerBasis

/-- `γ_i = 0` above the rank. -/
theorem chern_eq_zero_of_lt {i : ℕ} (hi : D.rank < i) : D.chern i = 0 :=
  @chernClass_eq_zero_of_lt (TotalHOf K X) (TotalHOf K P) D.commRing inferInstance D.algebra
    D.powerBasis i hi

end LerayHirschDataOf

end

end CharClass
end GroupApproximation
