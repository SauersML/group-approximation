import GroupApproximation.CharClass.ChernSplittingOfWhitney
import GroupApproximation.CharClass.SliceHomogeneousOf
import GroupApproximation.CharClass.SliceGenOfBlocks
import GroupApproximation.CharClass.SliceEsymm
import GroupApproximation.Meta.AxiomGuard

/-!
# The Chern classes of a split bundle over `K`, and their slice value

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm; the coefficient-generic form of
the algebra in `SliceValueV`.

Everything here is about abstract even-part Leray–Hirsch data `D : LerayHirschDataEvenOf K Y P`
(`CharClass/ChernClassesEvenOf`), so it depends on no geometry:

* **Whitney for one bundle.**  If the relation `∏_{l<r} (ξ + π^* y_l) = 0` holds on the
  projectivisation of the bundle itself, the Chern classes are the elementary symmetric functions
  of the `y_l`.  This is `ChernSplittingOf.splitPoly_of_splitRelation` and `chern_split_of_splitPoly`
  at the identity square.
* **The slice value.**  When the roots are zero on `n + 1` constant lines and carry the generator
  `gen j` on each of the `dd j` lines of the `j`-th block, the Chern classes are the coefficients of
  `sliceClass univ gen dd = ∏ⱼ (1 + gen j · X)^{dd j}`: reciprocal Vieta (`SliceEsymm`) and the
  block product at rank `n` (`SliceGenOfBlocks`).
* **Naturality.**  Leray–Hirsch data on a pullback square with compatible tautological classes has
  the pulled-back Chern classes (`ChernRelation.chernClass_map`).  This is how the slice class of
  the mapping torus reaches the Chern classes of `V`.

## Main declarations

* `evenTautOf_zero`, `evenMap_id_apply`, `nontrivial_evenPartOf`.
* `LerayHirschDataEvenOf.chern_eq_esymmOn_of_splitRelationOf` — **Whitney for one bundle.**
* `LerayHirschDataEvenOf.chern_eq_sliceClass_coeffOf` — **the slice value.**
* `LerayHirschDataEvenOf.chern_map_of_squareOf` — **naturality.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory Polynomial

noncomputable section

variable {K : Type} [CommRing K]

/-- The tautological even class of the zero class is zero. -/
theorem evenTautOf_zero {X : TopCat.{0}} : evenTautOf K (0 : Hmod K X 2) = 0 :=
  Subtype.ext (map_zero (TotalHOf.of K X 2))

/-- Pullback along the identity is the identity on the even part. -/
theorem evenMap_id_apply (X : TopCat.{0}) (a : Gen.evenPart K X) : Gen.evenMap K (𝟙 X) a = a :=
  Subtype.ext (ChernSplittingOf.totalHOf_map_id X (a : TotalHOf K X))

/-- The even part of a nontrivial cohomology ring is nontrivial. -/
theorem nontrivial_evenPartOf (X : TopCat.{0}) [Nontrivial (TotalHOf K X)] :
    Nontrivial (Gen.evenPart K X) :=
  ⟨⟨0, 1, fun h => zero_ne_one (α := TotalHOf K X) (congrArg Subtype.val h)⟩⟩

namespace LerayHirschDataEvenOf

/-- **Whitney for one bundle.**  The split relation on the projectivisation of the bundle itself
makes its Chern classes the elementary symmetric functions of the roots. -/
theorem chern_eq_esymmOn_of_splitRelationOf {Y P : TopCat.{0}} [Nontrivial (Gen.evenPart K Y)]
    (D : LerayHirschDataEvenOf K Y P) (r : ℕ) (hr : D.rank = r) (root : ℕ → Hmod K Y 2)
    (hrel : ∏ l ∈ Finset.range r,
      (evenTautOf K D.taut + Gen.evenMap K D.proj (evenTautOf K (root l))) = 0)
    (q : ℕ) :
    D.chern q = esymmOn (Finset.range r) (fun l => evenTautOf K (root l)) q := by
  have hsplit := ChernSplittingOf.splitPoly_of_splitRelation D D (𝟙 Y) (𝟙 P) (by simp)
    (ChernSplittingOf.totalHOf_map_id P _).symm r hr hr root hrel
  have h := ChernSplittingOf.chern_split_of_splitPoly D (𝟙 Y) r hr root hsplit q
  rwa [evenMap_id_apply] at h

/-- **The slice value.**  If the roots vanish on the `n + 1` constant lines and the root of every
line of the block `(j, i)` is `gen j`, the Chern classes are the coefficients of
`sliceClass univ gen dd`.  The block index is carried to the flat range by any equivalence `e`. -/
theorem chern_eq_sliceClass_coeffOf {Y P : TopCat.{0}} {ℓ : ℕ} (n : ℕ) (dd : Fin ℓ → ℕ)
    [Nontrivial (Gen.evenPart K Y)] (D : LerayHirschDataEvenOf K Y P)
    (e : (Fin (n + 1) ⊕ (Σ j : Fin ℓ, Fin (dd j))) ≃ Fin D.rank)
    (root : ℕ → Hmod K Y 2)
    (hrel : ∏ l ∈ Finset.range D.rank,
      (evenTautOf K D.taut + Gen.evenMap K D.proj (evenTautOf K (root l))) = 0)
    (gen : Fin ℓ → Gen.evenPart K Y)
    (hzero : ∀ i : Fin (n + 1), root (e (Sum.inl i) : ℕ) = 0)
    (hgen : ∀ b : Σ j : Fin ℓ, Fin (dd j), evenTautOf K (root (e (Sum.inr b) : ℕ)) = gen b.1)
    (q : ℕ) :
    D.chern q = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q := by
  have hesymm := D.chern_eq_esymmOn_of_splitRelationOf D.rank rfl root hrel q
  have hcoeff : (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q
      = esymmOn (Finset.range D.rank) (fun l => evenTautOf K (root l)) q := by
    rw [← coeff_prod_one_add_C_mul_X,
      prod_range_of_equiv D.rank e
        (fun k => 1 + Polynomial.C (evenTautOf K (root (e k : ℕ))) * Polynomial.X)
        (fun l => 1 + Polynomial.C (evenTautOf K (root l)) * Polynomial.X)
        (fun _ => rfl),
      Gen.prod_blocks_eq_sliceClass n dd gen
        (fun k => evenTautOf K (root (e k : ℕ)))
        (fun i => by
          show evenTautOf K (root (e (Sum.inl i) : ℕ)) = 0
          rw [hzero i, evenTautOf_zero])
        hgen]
  rw [hesymm, hcoeff]

/-- **Naturality of the Chern classes over `K`.**  Even-part Leray–Hirsch data on the two sides of
a commuting square, with the tautological class upstairs the pullback of the one downstairs and
equal ranks, has the pulled-back Chern classes. -/
theorem chern_map_of_squareOf {N F P P' : TopCat.{0}}
    [Nontrivial (Gen.evenPart K N)] [Nontrivial (Gen.evenPart K F)]
    (D : LerayHirschDataEvenOf K N P) (D' : LerayHirschDataEvenOf K F P')
    (proj : F ⟶ N) (q : P' ⟶ P) (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalHOf.of K P' 2 D'.taut = TotalHOf.map K q (TotalHOf.of K P 2 D.taut))
    (hr : D'.rank = D.rank) (k : ℕ) :
    D'.chern k = Gen.evenMap K proj (D.chern k) :=
  @chernClass_map (Gen.evenPart K N) (Gen.evenPart K F) (Gen.evenPart K P) (Gen.evenPart K P')
    _ _ D.algebra _ _ D'.algebra _ _ D.powerBasis D'.powerBasis (Gen.evenMap K proj) hr
    (ChernSplittingOf.aeval_taut_map D D' proj q hsq htaut) k

end LerayHirschDataEvenOf

end

#audit_axioms LerayHirschDataEvenOf.chern_eq_esymmOn_of_splitRelationOf
#audit_axioms LerayHirschDataEvenOf.chern_eq_sliceClass_coeffOf
#audit_axioms LerayHirschDataEvenOf.chern_map_of_squareOf

end GroupApproximation.CharClass
