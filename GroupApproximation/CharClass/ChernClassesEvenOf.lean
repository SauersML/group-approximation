import GroupApproximation.CharClass.LIXStepDGenRealEven
import GroupApproximation.CharClass.ChernRelation
import GroupApproximation.CharClass.LerayHirschAlgebra

/-!
# Chern classes over `K`, read in the even parts

The variant of `ChernClassesOf` that works at an odd prime over a base with odd cohomology.
`TotalHOf K X` is commutative only up to the Koszul sign, and over a base such as
`S¹ × S^{2n+1}` it is genuinely non-commutative, so `ChernClassesOf.LerayHirschDataOf`'s
commutativity field cannot be supplied there.  Chern classes live in even degrees, so they are
read in the **even parts** `Gen.evenPart K X` and `Gen.evenPart K P` of lix-evenside-n's
`LIXStepDGenRealEven`, which are commutative rings over every coefficient ring.

A Leray–Hirsch presentation restricts to the even parts because it is graded: `ξ` has degree 2,
so `π^*(a)·ξ^i` has the parity of `a`, and an even class of `P` has even Leray–Hirsch
coordinates.  So the data asks that `1, ξ, …, ξ^{r-1}` be a basis of `evenPart K P` over
`evenPart K X`, and nothing else: both rings are commutative and `Gen.evenMap K π` is a ring
homomorphism, so the algebra structure is `RingHom.toAlgebra` and no centrality hypothesis
appears.

**The root convention is not restated here.**  It is fixed once, in `ChernRelation`.

## Main declarations

* `evenTautOf`, `lhFunEvenOf`, `LerayHirschDataEvenOf`.
* `LerayHirschDataEvenOf.algebra`, `.powerBasis`, `.chern`, `.chernPolynomial`,
  `chernPolynomial_monic`, `aeval_taut_chernPolynomial`, `chern_zero`, `chern_eq_zero_of_lt`,
  `chern_isEven`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}}

/-- The tautological degree-2 class, as an element of the even part. -/
def evenTautOf (K : Type) [CommRing K] (ξ : Hmod K P 2) : Gen.evenPart K P :=
  ⟨TotalHOf.of K P 2 ξ, TotalHOf.isEven_of K P even_two ξ⟩

/-- The Leray–Hirsch combination `c ↦ ∑_{i<r} π^*(c i) · ξ^i` on the even parts. -/
def lhFunEvenOf (K : Type) [CommRing K] (π : P ⟶ X) (r : ℕ) (ξ : Hmod K P 2)
    (c : Fin r → Gen.evenPart K X) : Gen.evenPart K P :=
  ∑ i : Fin r, Gen.evenMap K π (c i) * evenTautOf K ξ ^ (i : ℕ)

/-- **Leray–Hirsch data over `K`, on the even parts**, for a rank-`r` projective bundle. -/
structure LerayHirschDataEvenOf (K : Type) [CommRing K] (X P : TopCat.{0}) where
  /-- The bundle projection. -/
  proj : P ⟶ X
  /-- The rank; the fibre is `ℂP^{rank-1}`. -/
  rank : ℕ
  /-- The Euler class of the (dual) tautological line, in degree 2. -/
  taut : Hmod K P 2
  /-- **Leray–Hirsch on the even parts**: `1, ξ, …, ξ^{rank-1}` is a basis of the even part of
  the total space over the even part of the base. -/
  free : Function.Bijective (lhFunEvenOf K proj rank taut)

namespace LerayHirschDataEvenOf

variable {K : Type} [CommRing K] (D : LerayHirschDataEvenOf K X P)

/-- The `evenPart K X`-algebra structure on `evenPart K P` induced by the projection. -/
@[reducible] def algebra : Algebra (Gen.evenPart K X) (Gen.evenPart K P) :=
  (Gen.evenMap K D.proj).toAlgebra

/-- The `PowerBasis` presented by even-part Leray–Hirsch data. -/
def powerBasis : @PowerBasis (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra :=
  @powerBasisOfBijective' (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra
    (evenTautOf K D.taut) D.rank (by exact D.free)

@[simp] theorem powerBasis_dim :
    @PowerBasis.dim (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra D.powerBasis
      = D.rank := rfl

@[simp] theorem powerBasis_gen :
    @PowerBasis.gen (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra D.powerBasis
      = evenTautOf K D.taut := rfl

/-- The **Chern classes** of the bundle over `K`, in the even part of the base. -/
def chern (i : ℕ) : Gen.evenPart K X :=
  @chernClass (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra D.powerBasis i

/-- The **total Chern polynomial** `X^r + γ_1 X^{r-1} + ⋯ + γ_r`. -/
def chernPolynomial : Polynomial (Gen.evenPart K X) :=
  @chernPoly (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra D.powerBasis

theorem chernPolynomial_monic : D.chernPolynomial.Monic :=
  @chernPoly_monic (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra D.powerBasis

/-- **The defining relation** `ξ^r + γ_1 ξ^{r-1} + ⋯ + γ_r = 0`, in the even part of the total
space. -/
theorem aeval_taut_chernPolynomial :
    @Polynomial.aeval (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra
      (evenTautOf K D.taut) D.chernPolynomial = 0 :=
  @aeval_gen_chernPoly (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra D.powerBasis

/-- `γ_0 = 1`. -/
theorem chern_zero [Nontrivial (Gen.evenPart K X)] : D.chern 0 = 1 :=
  @chernClass_zero (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra _ D.powerBasis

/-- `γ_i = 0` above the rank. -/
theorem chern_eq_zero_of_lt {i : ℕ} (hi : D.rank < i) : D.chern i = 0 :=
  @chernClass_eq_zero_of_lt (Gen.evenPart K X) (Gen.evenPart K P) _ _ D.algebra D.powerBasis
    i hi

/-- The Chern classes are even, in the form `RealBundleModP.γ_even` asks for. -/
theorem chern_isEven (i : ℕ) : TotalHOf.IsEven (D.chern i : TotalHOf K X) :=
  Gen.mem_evenPart.mp (D.chern i).2

end LerayHirschDataEvenOf

end

end CharClass
end GroupApproximation
