import GroupApproximation.CharClass.ChernClassesEvenOf
import GroupApproximation.CharClass.ChernSplittingOfPowers
import GroupApproximation.CharClass.ChernSplittingOfInjective

/-!
# The splitting principle over `K`, layer 2, items 3–5: Whitney on the flag bundle

Lane `lix-evenside`, prefix `CharClass/ChernSplittingOf*`.

The coefficient-generic port of `ChernWhitneyFlag` and `ChernFactorBridge`, on `lix-lh`'s
even-part carrier `LerayHirschDataEvenOf K X P` (`CharClass/ChernClassesEvenOf`).  No geometry
appears: once the pulled-back relation splits into linear factors, uniqueness of the monic
relation and Vieta give Whitney, and `SplittingDataOf` follows.

The split relation itself is a hypothesis here, written as the product it is
(`∏_{l<r} (ξ' + π'^* y_l) = 0` in the even part of the pulled-back projectivisation), so that the
statement depends on no name from the layer that proves it.

## Main results

* `ChernSplittingOf.chern_eq_coeff` — a Chern class is the named coefficient.
* `ChernSplittingOf.chern_split_of_splitPoly` — **Whitney on the flag bundle**, for every `k`.
* `ChernSplittingOf.splittingDataOf_of_splitPoly` — `SplittingDataOf` from the split polynomial.
* `ChernSplittingOf.aeval_taut_map`, `splitPoly_of_splitRelation` — the factorisation from the
  split relation on the pulled-back bundle.
* `ChernSplittingOf.hasSplittingP_of_splitRelation` — **the producer of `HasSplittingP`** for
  the Chern classes of `D`, from the split relation and the reduced powers.
-/

set_option autoImplicit false

open CategoryTheory Polynomial

namespace GroupApproximation.CharClass

namespace ChernSplittingOf

noncomputable section

variable {K : Type} [CommRing K]

/-- A Chern class is the coefficient of the relation in degree `rank − k`. -/
theorem chern_eq_coeff {N P : TopCat.{0}} (D : LerayHirschDataEvenOf K N P) {i : ℕ}
    (hi : i ≤ D.rank) : D.chern i = D.chernPolynomial.coeff (D.rank - i) :=
  @chernClass_of_le (Gen.evenPart K N) (Gen.evenPart K P) _ _ D.algebra D.powerBasis i hi

/-- **Whitney on the flag bundle.**  If the Chern polynomial splits into linear factors after
pullback, its coefficients are the elementary symmetric functions of the roots.  Above the rank
both sides vanish. -/
theorem chern_split_of_splitPoly {N F P : TopCat.{0}} (D : LerayHirschDataEvenOf K N P)
    (proj : F ⟶ N) (r : ℕ) (hr : D.rank = r) (root : ℕ → Hmod K F 2)
    (hsplit : D.chernPolynomial.map (Gen.evenMap K proj)
      = ∏ l ∈ Finset.range r, (X + C (evenTautOf K (root l))))
    (k : ℕ) :
    Gen.evenMap K proj (D.chern k)
      = esymmOn (Finset.range r) (fun l => evenTautOf K (root l)) k := by
  subst hr
  by_cases hk : k ≤ D.rank
  · have hcoeff : Gen.evenMap K proj (D.chern k)
        = (D.chernPolynomial.map (Gen.evenMap K proj)).coeff (D.rank - k) := by
      rw [Polynomial.coeff_map, chern_eq_coeff D hk]
    rw [hcoeff, hsplit,
      Finset.prod_X_add_C_coeff _ _ (by rw [Finset.card_range]; omega), esymmOn_def]
    congr 2
    rw [Finset.card_range]
    omega
  · replace hk : D.rank < k := by omega
    have h1 : D.chern k = 0 := D.chern_eq_zero_of_lt hk
    have h2 : esymmOn (Finset.range D.rank) (fun l => evenTautOf K (root l)) k = 0 := by
      rw [esymmOn_def,
        Finset.powersetCard_eq_empty.mpr (by rw [Finset.card_range]; omega)]
      exact Finset.sum_empty
    rw [h1, h2, map_zero]

/-- **`SplittingDataOf` from the split polynomial.** -/
def splittingDataOf_of_splitPoly {N F P : TopCat.{0}} (D : LerayHirschDataEvenOf K N P)
    (proj : F ⟶ N) (hinj : Function.Injective (TotalHOf.map K proj)) (r : ℕ) (hr : D.rank = r)
    (root : ℕ → Hmod K F 2)
    (hsplit : D.chernPolynomial.map (Gen.evenMap K proj)
      = ∏ l ∈ Finset.range r, (X + C (evenTautOf K (root l)))) :
    SplittingDataOf K N F r D.chern where
  proj := proj
  root := root
  pull_injective := hinj
  chern_split := chern_split_of_splitPoly D proj r hr root hsplit

/-- **The pulled-back relation still holds upstairs**, from the commuting square and the
compatibility of the tautological classes. -/
theorem aeval_taut_map {N F P P' : TopCat.{0}} (D : LerayHirschDataEvenOf K N P)
    (D' : LerayHirschDataEvenOf K F P') (proj : F ⟶ N) (q : P' ⟶ P)
    (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalHOf.of K P' 2 D'.taut = TotalHOf.map K q (TotalHOf.of K P 2 D.taut)) :
    @Polynomial.aeval (Gen.evenPart K F) (Gen.evenPart K P') _ _ D'.algebra
        (evenTautOf K D'.taut) (D.chernPolynomial.map (Gen.evenMap K proj)) = 0 := by
  have hkey : (Gen.evenMap K D'.proj).comp (Gen.evenMap K proj)
      = (Gen.evenMap K q).comp (Gen.evenMap K D.proj) := by
    refine RingHom.ext fun a => Subtype.ext ?_
    show TotalHOf.map K D'.proj (TotalHOf.map K proj a)
      = TotalHOf.map K q (TotalHOf.map K D.proj a)
    rw [← totalHOf_map_comp, ← totalHOf_map_comp, hsq]
  have htaut' : evenTautOf K D'.taut = Gen.evenMap K q (evenTautOf K D.taut) :=
    Subtype.ext htaut
  have hz : Polynomial.eval₂ (Gen.evenMap K D.proj) (evenTautOf K D.taut)
      D.chernPolynomial = 0 := D.aeval_taut_chernPolynomial
  show Polynomial.eval₂ (Gen.evenMap K D'.proj) (evenTautOf K D'.taut)
      (D.chernPolynomial.map (Gen.evenMap K proj)) = 0
  rw [Polynomial.eval₂_map, hkey, htaut',
    ← Polynomial.hom_eval₂ D.chernPolynomial (Gen.evenMap K D.proj) (Gen.evenMap K q)
      (evenTautOf K D.taut), hz, map_zero]

/-- **The factorisation.**  From the split relation on the pulled-back projective bundle, the
Chern polynomial factors after pullback. -/
theorem splitPoly_of_splitRelation {N F P P' : TopCat.{0}}
    [Nontrivial (Gen.evenPart K N)] [Nontrivial (Gen.evenPart K F)]
    (D : LerayHirschDataEvenOf K N P) (D' : LerayHirschDataEvenOf K F P')
    (proj : F ⟶ N) (q : P' ⟶ P) (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalHOf.of K P' 2 D'.taut = TotalHOf.map K q (TotalHOf.of K P 2 D.taut))
    (r : ℕ) (hr : D.rank = r) (hr' : D'.rank = r) (root : ℕ → Hmod K F 2)
    (hrel : ∏ l ∈ Finset.range r,
      (evenTautOf K D'.taut + Gen.evenMap K D'.proj (evenTautOf K (root l))) = 0) :
    D.chernPolynomial.map (Gen.evenMap K proj)
      = ∏ l ∈ Finset.range r, (X + C (evenTautOf K (root l))) := by
  have h1 : D'.chernPolynomial = ∏ l ∈ Finset.range r, (X + C (evenTautOf K (root l))) :=
    @chernPoly_eq_prod_of_root (Gen.evenPart K F) (Gen.evenPart K P') _ _ D'.algebra _ ℕ
      D'.powerBasis (Finset.range r) (fun l => evenTautOf K (root l))
      (by rw [Finset.card_range]; exact hr'.symm) hrel
  have h2 : D'.chernPolynomial = D.chernPolynomial.map (Gen.evenMap K proj) :=
    @chernPoly_map (Gen.evenPart K N) (Gen.evenPart K F) (Gen.evenPart K P) (Gen.evenPart K P')
      _ _ D.algebra _ _ D'.algebra _ _ D.powerBasis D'.powerBasis (Gen.evenMap K proj)
      (hr'.trans hr.symm) (aeval_taut_map D D' proj q hsq htaut)
  rw [← h2, h1]

/-- **The producer of `HasSplittingP` for the Chern classes of `D`.**  A second Leray–Hirsch datum
`D'` on the pullback of the bundle to a space `F`, with the split relation there, an injective
pullback `F → N`, and the reduced powers on `N` and `F` give the splitting principle at the prime
`p` for `D.chern`. -/
theorem hasSplittingP_of_splitRelation {N F P P' : TopCat.{0}} {p : ℕ}
    [Nontrivial (Gen.evenPart K N)] [Nontrivial (Gen.evenPart K F)]
    (D : LerayHirschDataEvenOf K N P) (D' : LerayHirschDataEvenOf K F P')
    (proj : F ⟶ N) (q : P' ⟶ P) (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalHOf.of K P' 2 D'.taut = TotalHOf.map K q (TotalHOf.of K P 2 D.taut))
    (hinj : Function.Injective (TotalHOf.map K proj))
    (r : ℕ) (hr : D.rank = r) (hr' : D'.rank = r) (root : ℕ → Hmod K F 2)
    (hrel : ∏ l ∈ Finset.range r,
      (evenTautOf K D'.taut + Gen.evenMap K D'.proj (evenTautOf K (root l))) = 0)
    (PN : ℕ → TotalHOf K N →+ TotalHOf K N)
    (hPN : ∀ (i : ℕ) (x : TotalHOf K N), TotalHOf.IsEven x → TotalHOf.IsEven (PN i x))
    (PF : ℕ → TotalHOf K F →+ TotalHOf K F)
    (hPF : ∀ (i : ℕ) (x : TotalHOf K F), TotalHOf.IsEven x → TotalHOf.IsEven (PF i x))
    (hzero : ∀ x : TotalHOf K F, PF 0 x = x)
    (hcartan : ∀ (i : ℕ) (u v : TotalHOf K F),
      PF i (u * v) = ∑ j ∈ Finset.range (i + 1), PF j u * PF (i - j) v)
    (m : ℤ)
    (hone : ∀ h : TotalPieceOf K F 2,
      PF 1 (TotalHOf.of K F 2 h) = (m : TotalHOf K F) * TotalHOf.of K F 2 h ^ p)
    (hhigh : ∀ (h : TotalPieceOf K F 2) (j : ℕ), 2 ≤ j → PF j (TotalHOf.of K F 2 h) = 0)
    (hnat : ∀ (i : ℕ) (x : TotalHOf K N),
      PF i (TotalHOf.map K proj x) = TotalHOf.map K proj (PN i x)) :
    ParityP.HasSplittingP p D.chern (fun i => Gen.evenRestrictAdd (PN i) (hPN i)) m :=
  hasSplittingP_of_splittingDataOf
    (splittingDataOf_of_splitPoly D proj hinj r hr root
      (splitPoly_of_splitRelation D D' proj q hsq htaut r hr hr' root hrel))
    PN hPN PF hPF hzero hcartan m hone hhigh hnat

end

end ChernSplittingOf

end GroupApproximation.CharClass
