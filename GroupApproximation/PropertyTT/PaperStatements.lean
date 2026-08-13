import GroupApproximation.PropertyTT.BoundedGeneration
import GroupApproximation.PropertyTT.FiniteTypeLeavittTT
import GroupApproximation.PropertyTT.RankFourRelativeTT
import GroupApproximation.Leavitt.UniversalLeavitt
import Mathlib.RingTheory.FiniteType

/-!
# Paper statements for strong-division rings and `(TT)/T`

This file is the rigidity paper's public theorem surface.  Each declaration
has the exact hypotheses and conclusion of its numbered manuscript theorem.
It contains no nonsoficity input; the combined nonsofic corollary belongs in a
separate endpoint so that the rigidity theorem has an independent dependency
closure.
-/

namespace GroupApproximation
namespace PropertyTTPaper

open FreeRootCharacterValuation

noncomputable section

abbrev BinaryL := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

universe u v

/-- **Strong relative root theorem.**  Over the free associative `ZMod 2`
algebra, every Hilbert-space quasi-cocycle is bounded on the `(0, 3)`
elementary root subgroup.  No hypothesis excluding invariant vectors is used.

This is deliberately stated as `HasRelativeTT`, rather than merely relative
`(TT)/T`, so that the public theorem records the stronger conclusion proved by
the rank-four argument. -/
theorem freeCharacteristicTwo_root_hasRelativeTT
    (X : Type) [Fintype X] :
    HasRelativeTT.{0, v}
      (elementaryGroup (Fin 4) (FreeAlgebra (ZMod 2) X))
      (elementaryRootSubgroup (0 : Fin 4) 3 (by decide)) :=
  RankFourRelativeTT.hasRelativeTT_X03 X

/-- **Localized rank-three plane estimate.**  Control of the two unit
translations in a common-terminal-index plane and of the unit and free
generators in the two adjacent root directions controls every displacement
in that plane.  This is the quantitative Fourier input used by the direct
rank-four root proof. -/
theorem freeCharacteristicTwo_localizedPlaneEstimate
    (X : Type) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) X) →*
      (E ≃ₗᵢ[ℂ] E))
    (z : E) {B : ℝ} (hB : 0 ≤ B)
    (hIK : ‖rho (elementaryRoot i k hik 1) z - z‖ ≤ B)
    (hJK : ‖rho (elementaryRoot j k hjk 1) z - z‖ ≤ B)
    (hIJUnit : ‖rho (elementaryRoot i j hij 1) z - z‖ ≤ B)
    (hJIUnit : ‖rho (elementaryRoot j i hij.symm 1) z - z‖ ≤ B)
    (hIJGen : ∀ q : Fin (Fintype.card X),
      ‖rho (elementaryRoot i j hij
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖ ≤ B)
    (hJIGen : ∀ q : Fin (Fintype.card X),
      ‖rho (elementaryRoot j i hij.symm
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖ ≤ B)
    (g : elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) X))
    (hg : g ∈ elementaryRootSubgroup i k hik ⊔
      elementaryRootSubgroup j k hjk) :
    ‖rho g z - z‖ ≤
      2 * (6 * Fintype.card X + 6 : ℝ) * B :=
  norm_comp_columnPlane_sub_le_of_root_bounds X
    i j k hij hik hjk (MonoidHom.id _) rho z hB hIK hJK hIJUnit hJIUnit
    hIJGen hJIGen g hg

/-- **Limiting Fourier energy estimate.**  The moving mass of the full
two-root plane is bounded by the unit-root errors and the adjacent unit and
free-generator errors.  Its proof is the finite-stage character-mass
decomposition followed by the two telescoping boundary limits. -/
theorem freeCharacteristicTwo_planeEnergyEstimate
    (X : Type) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) X) →*
      (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2 ≤
      ‖rho (elementaryRoot i k hik 1) z - z‖ ^ 2 +
        ‖rho (elementaryRoot j k hjk 1) z - z‖ ^ 2 +
        (3 : ℝ) / 2 *
          ((∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot j i hij.symm
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
            ∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot i j hij
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ +
          2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ :=
  norm_joinRootMovingProjection_sq_le_explicit_errors
    X i j k hij hik hjk rho z

/-- **Row-plane transport.**  In characteristic two, inverse transpose with
word reversal sends every unit or free-generator root in the source rank
three group to the opposite root in the upper-left rank-four block. -/
theorem freeCharacteristicTwo_rowEmbedding_controlRoot
    (X : Type) [Fintype X]
    (i j : Fin 3) (hij : i ≠ j)
    (q : Option (Fin (Fintype.card X))) :
    RankFourRootGeometry.embedRow012 X
        (elementaryRoot i j hij
          (FreeElementaryPropertyT.controlCoefficient X q)) =
      elementaryRoot (Fin.castAdd 1 j) (Fin.castAdd 1 i)
        ((Fin.castAddEmb 1).injective.ne hij.symm)
        (FreeElementaryPropertyT.controlCoefficient X q) :=
  RankFourRootGeometry.embedRow012_controlRoot X i j hij q

/-- **Inverse-transpose root formula.**  Word reversal followed by inverse
transpose is an automorphism of the rank-three elementary group.  On an
arbitrary elementary root it reverses the root and applies signed word
reversal to the coefficient. -/
theorem freeCharacteristicTwo_inverseTranspose_root
    (X : Type)
    (i j : Fin 3) (hij : i ≠ j)
    (a : FreeAlgebra (ZMod 2) X) :
    FreeElementaryTranspose.elementaryTransposeEquiv X (Fin 3)
        (elementaryRoot i j hij a) =
      elementaryRoot j i hij.symm
        (-MulOpposite.unop
          (FreeAlgebra.reverseEquiv (ZMod 2) X a)) :=
  FreeElementaryTranspose.elementaryTransposeEquiv_elementaryRoot
    X (Fin 3) i j hij a

/-- **Arbitrary row-root transport.**  The inverse-transposed upper-left
rank-three embedding sends an arbitrary root to the opposite row root with
signed reversed coefficient. -/
theorem freeCharacteristicTwo_rowEmbedding_elementaryRoot
    (X : Type)
    (i j : Fin 3) (hij : i ≠ j)
    (a : FreeAlgebra (ZMod 2) X) :
    RankFourRootGeometry.embedRow012 X
        (elementaryRoot i j hij a) =
      elementaryRoot (Fin.castAdd 1 j) (Fin.castAdd 1 i)
        ((Fin.castAddEmb 1).injective.ne hij.symm)
        (-MulOpposite.unop
          (FreeAlgebra.reverseEquiv (ZMod 2) X a)) :=
  RankFourRootGeometry.embedRow012_elementaryRoot X i j hij a

/-- **Coordinate-block factorization.**  If every nonzero element of `R`
admits a single sandwich to `1`, then every invertible `n × n` matrix is a
product of at most `2*n+2` factors, each either an elementary transvection or
an element of the fixed coordinate block omitting `j`.

This is not a claim of bounded elementary generation: one coordinate copy of
`GL_(n-1)(R)` is part of the generating set. -/
theorem coordinateBlock_factorization
    (R : Type*) [Ring R] [Nontrivial R]
    (n : ℕ) (hn : 2 ≤ n)
    (hdiv : HasSingleSandwichDivision R) (j : Fin n) :
    IsBoundedProduct (Matrix (Fin n) (Fin n) R)ˣ
      (coordinateBlockOrRoot j) (2 * n + 2) := by
  letI : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [Fintype.card_fin]
      exact hn)
  simpa using
    (boundedProduct_coordinateBlockOrRoot (R := R) hdiv j)

/-- **Three-move diagonal pivot.**  For two distinct coordinates, one
elementary left factor and two elementary right factors suffice to create a
literal `1` at the second diagonal coordinate.  The off-diagonal entries are
left for the full clearing sweeps. -/
theorem threeMove_diagonalPivot
    (R ι : Type*) [Ring R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι]
    (hdiv : HasSingleSandwichDivision R)
    (A : (Matrix ι ι R)ˣ) (i j : ι) (hij : i ≠ j) :
    ∃ E F : (Matrix ι ι R)ˣ,
      ((E * A * F : (Matrix ι ι R)ˣ) : Matrix ι ι R) j j = 1 ∧
      ∃ l r : List (Matrix ι ι R)ˣ,
        l.length ≤ 1 ∧ r.length ≤ 2 ∧
        (∀ x ∈ l, IsElementaryUnit x) ∧
        (∀ x ∈ r, IsElementaryUnit x) ∧
        l.prod = E ∧ r.prod = F :=
  exists_three_move_diagonal_pivot hdiv A i j hij

/-- **Elementary/general-linear identification.**  Binary Leavitt
self-similarity transports the rank-two diagonal reduction to every rank. -/
theorem elementaryGroup_eq_generalLinear
    (R : Type) [Ring R] [Nontrivial R]
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R)
    (n : ℕ) (hn : 2 ≤ n) :
    elementaryGroup (Fin n) R = ⊤ :=
  FiniteTypeLeavittTT.elementaryGroup_eq_top L hdiv hdiag n hn

/-- **Leavitt rank equivalence.**  A binary Leavitt family identifies all
elementary matrix groups of ranks at least two. -/
noncomputable def leavitt_elementaryRankEquivalence
    (R : Type) [Ring R]
    (L : LeavittFamily R)
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    elementaryGroup (Fin n) R ≃* elementaryGroup (Fin m) R := by
  cases n with
  | zero => omega
  | succ n =>
      cases m with
      | zero => omega
      | succ m =>
          exact L.rankSuccEquiv n m (by omega) (by omega)

/-- **Bidirectional block flattening.**  If the outer index type has two
distinct elements, block flattening identifies the full elementary group
over a matrix ring with the elementary group over the product index type. -/
noncomputable def elementaryBlockFlattening
    (R ι κ : Type) [Ring R]
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    [Fintype κ] [DecidableEq κ] :
    elementaryGroup ι (Matrix κ κ R) ≃*
      elementaryGroup (ι × κ) R :=
  elementaryBlockEquiv

/-- **Kazhdan normalized-set globalization.**  If a Kazhdan group is
generated by a set on which quasi-cocycles are bounded, then that control
extends to every subgroup normalizing the set. -/
theorem kazhdan_normalizedSet_globalization
    {G : Type u} [Group G]
    (H : Subgroup G) (S : Set G)
    (hT : HasKazhdanPropertyT.{u, v} G)
    (hgen : Subgroup.closure S = ⊤)
    (hnormalizes : ∀ h : G, h ∈ H → ∀ s ∈ S, h⁻¹ * s * h ∈ S)
    (hrelS : HasRelativeTTmodTOnSet.{u, v} G S) :
    HasRelativeTTmodT.{u, v} G H :=
  hasRelativeTTmodT_of_kazhdan_of_normalized_set
    H S hT hgen hnormalizes hrelS

/-- **Rank-four synthesis.**  The finite-presentation form of the structural
hypotheses already gives global `(TT)/T` in rank four. -/
theorem finiteFreeQuotient_rankFour_hasTTmodT
    (R : Type) [Ring R] [Nontrivial R]
    (X : Type) [Fintype X]
    (f : FreeAlgebra (ZMod 2) X →+* R)
    (hf : Function.Surjective f)
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R) :
    HasTTmodT.{0, v} (elementaryGroup (Fin 4) R) :=
  FiniteTypeLeavittTT.rankFour_hasTTmodT X f hf L hdiv hdiag

/-- **Product estimate used in bounded generation.**  This is deliberately
the empty-list-safe inequality proved by the implementation. -/
theorem quasiCocycle_list_product_bound
    {G : Type u} [Group G]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D C : ℝ}
    (hb : IsQuasiCocycle rho b D) (l : List G)
    (hl : ∀ g ∈ l, ‖b g‖ ≤ C) :
    ‖b l.prod‖ ≤ (l.length : ℝ) * C + (l.length + 1 : ℕ) * D :=
  hb.norm_list_prod_le l hl

/-- **Four-hypothesis synthesis theorem.**  A finite free characteristic-two
presentation, binary Leavitt self-similarity, single-sandwich division, and
trivial elementary diagonal class together imply `(TT)/T` in every
elementary rank at least two. -/
theorem finiteFreeQuotient_elementaryGroup_hasTTmodT
    (R : Type) [Ring R] [Nontrivial R]
    (X : Type) [Fintype X]
    (f : FreeAlgebra (ZMod 2) X →+* R)
    (hf : Function.Surjective f)
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R)
    (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, v} (elementaryGroup (Fin n) R) :=
  FiniteTypeLeavittTT.elementaryGroup_hasTTmodT
    X f hf L hdiv hdiag n hn

/-- **Finite-type synthesis wrapper.**  This is the preceding theorem in
standard mathematical language.  Finite type is used only to construct the
finite free-algebra surjection; the other three structural assumptions remain
explicit. -/
theorem finiteType_elementaryGroup_hasTTmodT
    (R : Type) [Ring R] [Nontrivial R] [Algebra (ZMod 2) R]
    [Algebra.FiniteType (ZMod 2) R]
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R)
    (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, v} (elementaryGroup (Fin n) R) := by
  obtain ⟨s, hs⟩ :=
    (Algebra.FiniteType.out : (⊤ : Subalgebra (ZMod 2) R).FG)
  let f : FreeAlgebra (ZMod 2) {x : R // x ∈ s} →ₐ[ZMod 2] R :=
    FreeAlgebra.lift (ZMod 2) Subtype.val
  have hrange : f.range = ⊤ := by
    change (FreeAlgebra.lift (ZMod 2)
      (Subtype.val : {x : R // x ∈ s} → R)).range = ⊤
    rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift]
    have hcoe : Set.range (Subtype.val : {x : R // x ∈ s} → R) =
        (s : Set R) := by
      ext x
      simp
    rw [hcoe]
    exact hs
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ f.range := by simp [hrange]
    exact hy
  exact finiteFreeQuotient_elementaryGroup_hasTTmodT
    R {x : R // x ∈ s} f.toRingHom hf L hdiv hdiag n hn

/-- **Binary Leavitt specialization.**  In every rank at least two, the
elementary group over the binary Leavitt algebra over `F₂` has property
`(TT)/T`. -/
theorem binaryLeavitt_elementaryGroup_hasTTmodT
    (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, v}
      (elementaryGroup (Fin n) BinaryL) :=
  FiniteTypeLeavittTT.elementaryGroup_hasTTmodT
    BinaryLeavitt.Generator
    (BinaryLeavitt.quotientMap (ZMod 2)).toRingHom
    (RingQuot.mkAlgHom_surjective (ZMod 2)
      (BinaryLeavitt.Relation (ZMod 2)))
    (BinaryLeavitt.family (ZMod 2))
    (BinaryLeavitt.hasSingleSandwichDivision (ZMod 2))
    (BinaryLeavitt.hasElementaryDiagonalClass (ZMod 2))
    n hn

/-- **Leavitt rank collapse.**  Matrix self-similarity and `GL = EL`
identify every elementary rank at least two with the unit group itself. -/
noncomputable def binaryLeavitt_elementaryEquivUnits
    (n : ℕ) (hn : 2 ≤ n) :
    elementaryGroup (Fin n) BinaryL ≃* BinaryLˣ := by
  let m := n - 1
  have hnm : n = m + 1 := by
    dsimp [m]
    omega
  rw [hnm]
  exact ((MulEquiv.subgroupCongr
      (FiniteTypeLeavittTT.elementaryGroup_eq_top
        (BinaryLeavitt.family (ZMod 2))
        (BinaryLeavitt.hasSingleSandwichDivision (ZMod 2))
        (BinaryLeavitt.hasElementaryDiagonalClass (ZMod 2))
        (m + 1) (by omega))).trans Subgroup.topEquiv).trans
    ((BinaryLeavitt.family (ZMod 2)).prefixUnitsEquiv (leftCombCode m)
      ((BinaryLeavitt.family (ZMod 2)).leftCombCode_complete m))

/-- **Unit-group form of the binary Leavitt theorem.**  The unit group of
`L_{F₂}(1,2)` has property `(TT)/T`. -/
theorem binaryLeavittUnits_hasTTmodT :
    HasTTmodT.{0, v} BinaryLˣ :=
  HasTTmodT.of_mulEquiv
    (binaryLeavitt_elementaryEquivUnits 2 (by omega)).symm
    (binaryLeavitt_elementaryGroup_hasTTmodT 2 (by omega))

end
end PropertyTTPaper
end GroupApproximation
