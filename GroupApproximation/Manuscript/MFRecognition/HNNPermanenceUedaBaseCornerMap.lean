import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBaseCornerElement

/-! # The base algebra as a subalgebra of Ueda's corner

Each structure field below follows the same two-layer discipline as
`HNNPermanenceUedaBaseCornerElement`: the two-by-two identity is proved at an
abstract entry algebra, where the landed `CStarMatrixTwo` and
`HNNPermanenceUedaOperations` lemmas match syntactically, and it is carried
across the left factor map by `congrArg` composed with the corresponding
`map_*` lemma.  At the concrete algebras of a `CoronaConjugator` the `star`
and `*` produced by the `map_*` lemmas are instantiated from the
homomorphism's own structure rather than from `CStarMatrix`'s `StarRing` and
`Semiring`, so a rewrite chain through them has nothing to match; the two
spellings are definitionally equal, which is what `exact` accepts. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## The diagonal corner at an abstract entry algebra -/

theorem diagonalZero_mul_diagonalZero {K : Type} [CStarAlgebra K] (d e : K) :
    cStarDiagonalTwo d (0 : K) * cStarDiagonalTwo e 0 =
      cStarDiagonalTwo (d * e) 0 := by
  rw [cStarDiagonalTwo_mul, zero_mul]

theorem diagonalZero_add_diagonalZero {K : Type} [CStarAlgebra K] (d e : K) :
    cStarDiagonalTwo d (0 : K) + cStarDiagonalTwo e 0 =
      cStarDiagonalTwo (d + e) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagonalZero_zero {K : Type} [CStarAlgebra K] :
    cStarDiagonalTwo (0 : K) 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem star_diagonalZero {K : Type} [CStarAlgebra K] (d : K) :
    star (cStarDiagonalTwo d (0 : K)) = cStarDiagonalTwo (star d) 0 := by
  rw [star_cStarDiagonalTwo, star_zero]

theorem diagonalZero_algebraMap {K : Type} [CStarAlgebra K] (r : ℂ) :
    cStarDiagonalTwo (algebraMap ℂ K r) 0 =
      r • cStarMatrixUnitTwo 0 0 (1 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cStarDiagonalTwo, cStarMatrixUnitTwo,
      Algebra.algebraMap_eq_smul_one]

/-! ## The canonical map `D → ePe` -/

/-- The canonical unital star-algebra homomorphism `D → ePe`. -/
def cornerBaseMap (data : CoronaConjugator G S T phi A X) :
    baseAlgebra data →⋆ₐ[ℂ]
      CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data) where
  toFun := cornerBaseElement data
  map_one' := by
    apply Subtype.ext
    change amalgamLeft data (cStarDiagonalTwo 1 0) = cornerUnit data
    exact congrArg (amalgamLeft data) cStarDiagonalTwo_one_zero
  map_mul' d e := by
    apply Subtype.ext
    change amalgamLeft data (cStarDiagonalTwo (d * e) 0) =
      amalgamLeft data (cStarDiagonalTwo d 0) *
        amalgamLeft data (cStarDiagonalTwo e 0)
    exact (congrArg (amalgamLeft data)
        (diagonalZero_mul_diagonalZero d e).symm).trans
      (map_mul (amalgamLeft data) (cStarDiagonalTwo d 0)
        (cStarDiagonalTwo e 0))
  map_zero' := by
    apply Subtype.ext
    change amalgamLeft data (cStarDiagonalTwo 0 0) = 0
    exact (congrArg (amalgamLeft data) diagonalZero_zero).trans
      (map_zero (amalgamLeft data))
  map_add' d e := by
    apply Subtype.ext
    change amalgamLeft data (cStarDiagonalTwo (d + e) 0) =
      amalgamLeft data (cStarDiagonalTwo d 0) +
        amalgamLeft data (cStarDiagonalTwo e 0)
    exact (congrArg (amalgamLeft data)
        (diagonalZero_add_diagonalZero d e).symm).trans
      (map_add (amalgamLeft data) (cStarDiagonalTwo d 0)
        (cStarDiagonalTwo e 0))
  commutes' r := by
    apply Subtype.ext
    change amalgamLeft data (cStarDiagonalTwo (algebraMap ℂ _ r) 0) =
      r • amalgamLeft data (cStarMatrixUnitTwo 0 0 1)
    exact (congrArg (amalgamLeft data) (diagonalZero_algebraMap r)).trans
      (map_smul (amalgamLeft data) r (cStarMatrixUnitTwo 0 0 1))
  map_star' d := by
    apply Subtype.ext
    change amalgamLeft data (cStarDiagonalTwo (star d) 0) =
      star (amalgamLeft data (cStarDiagonalTwo d 0))
    exact (congrArg (amalgamLeft data) (star_diagonalZero d).symm).trans
      (map_star (amalgamLeft data) (cStarDiagonalTwo d 0))

@[simp] theorem coe_cornerBaseMap
    (data : CoronaConjugator G S T phi A X) (d : baseAlgebra data) :
    ((cornerBaseMap data d :
      CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data)) : amalgam data) =
      amalgamLeft data (cStarDiagonalTwo d 0) :=
  rfl

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
