import GroupApproximation.CharClass.ChernSplittingOfWhitney

/-!
# The splitting principle over `K`, layer 2, item 6: the flag-bundle assembly

Lane `lix-evenside`, prefix `CharClass/ChernSplittingOf*`.

`ChernSplittingOfWhitney.hasSplittingP_of_splitRelation` is stated for abstract Leray–Hirsch data
and an abstract square.  This file specialises it to the geometry that supplies those inputs: a
bundle `E` over `X`, its flag space `Flag E r`, the projectivisation of `E` and of its pullback to
the flag space, and the square they form.  The square commutes on the nose and the injectivity
of the flag pullback is the tower induction of `ChernSplittingOfInjective`.

What remains a hypothesis is exactly what the Leray–Hirsch layer over `K` and the odd-primary
operations deliver:

* the two even-part Leray–Hirsch data, with their projections the bundle projections;
* the compatibility of the tautological classes along `projComap`;
* degreewise injectivity of the pullback along each projective bundle of the tower below the
  height (Leray–Hirsch at each `flagRest E n`);
* the split relation on the pulled-back projectivisation;
* the reduced powers on `X` and on the flag space.

## Main results

* `ChernSplittingOf.flag_square` — the square of projections commutes.
* `ChernSplittingOf.hasSplittingP_flag` — **`HasSplittingP` for the Chern classes of a bundle**.
-/

set_option autoImplicit false

open CategoryTheory

namespace GroupApproximation.CharClass

namespace ChernSplittingOf

noncomputable section

variable {K : Type} [CommRing K] {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **The flag square commutes**: projecting the pulled-back projectivisation to the flag space and
then to `X` is projecting it to the projectivisation of `E` and then to `X`. -/
theorem flag_square (E : Bundle X ι) (r : ℕ) :
    cmap (Bundle.projPi (Bundle.comap (Bundle.flagProj E r) E)) ≫ cmap (Bundle.flagProj E r)
      = cmap (Bundle.projComap (Bundle.flagProj E r) E) ≫ cmap (Bundle.projPi E) := by
  apply TopCat.ext
  intro z
  rfl

/-- **The splitting principle over `K` for the Chern classes of a bundle, at the prime `p`.**
The even-part Leray–Hirsch data of `E` and of its pullback to the flag space, the compatibility of
their tautological classes, Leray–Hirsch injectivity at each stage of the flag tower, the split
relation upstairs, and the reduced powers give `HasSplittingP` for `D.chern`, with the reduced
powers of `X` restricted to the even part. -/
theorem hasSplittingP_flag {p : ℕ} (E : Bundle X ι) (r : ℕ)
    [Nontrivial (Gen.evenPart K (TopCat.of X))]
    [Nontrivial (Gen.evenPart K (TopCat.of (Bundle.Flag E r)))]
    (D : LerayHirschDataEvenOf K (TopCat.of X) (TopCat.of (Bundle.Proj E)))
    (hD : D.proj = cmap (Bundle.projPi E)) (hDr : D.rank = r)
    (D' : LerayHirschDataEvenOf K (TopCat.of (Bundle.Flag E r))
      (TopCat.of (Bundle.Proj (Bundle.comap (Bundle.flagProj E r) E))))
    (hD' : D'.proj = cmap (Bundle.projPi (Bundle.comap (Bundle.flagProj E r) E)))
    (hD'r : D'.rank = r)
    (htaut : TotalHOf.of K (TopCat.of (Bundle.Proj (Bundle.comap (Bundle.flagProj E r) E))) 2
        D'.taut
      = TotalHOf.map K (cmap (Bundle.projComap (Bundle.flagProj E r) E))
          (TotalHOf.of K (TopCat.of (Bundle.Proj E)) 2 D.taut))
    (hstage : ∀ n : ℕ, n < r → ∀ k : ℕ,
      Function.Injective (pull (K := K) (cmap (Bundle.projPi (Bundle.flagRest E n))) k))
    (root : ℕ → Hmod K (TopCat.of (Bundle.Flag E r)) 2)
    (hrel : ∏ l ∈ Finset.range r,
      (evenTautOf K D'.taut + Gen.evenMap K D'.proj (evenTautOf K (root l))) = 0)
    (PN : ℕ → TotalHOf K (TopCat.of X) →+ TotalHOf K (TopCat.of X))
    (hPN : ∀ (i : ℕ) (x : TotalHOf K (TopCat.of X)),
      TotalHOf.IsEven x → TotalHOf.IsEven (PN i x))
    (PF : ℕ → TotalHOf K (TopCat.of (Bundle.Flag E r)) →+ TotalHOf K (TopCat.of (Bundle.Flag E r)))
    (hPF : ∀ (i : ℕ) (x : TotalHOf K (TopCat.of (Bundle.Flag E r))),
      TotalHOf.IsEven x → TotalHOf.IsEven (PF i x))
    (hzero : ∀ x : TotalHOf K (TopCat.of (Bundle.Flag E r)), PF 0 x = x)
    (hcartan : ∀ (i : ℕ) (u v : TotalHOf K (TopCat.of (Bundle.Flag E r))),
      PF i (u * v) = ∑ j ∈ Finset.range (i + 1), PF j u * PF (i - j) v)
    (m : ℤ)
    (hone : ∀ h : TotalPieceOf K (TopCat.of (Bundle.Flag E r)) 2,
      PF 1 (TotalHOf.of K _ 2 h)
        = (m : TotalHOf K (TopCat.of (Bundle.Flag E r))) * TotalHOf.of K _ 2 h ^ p)
    (hhigh : ∀ (h : TotalPieceOf K (TopCat.of (Bundle.Flag E r)) 2) (j : ℕ), 2 ≤ j →
      PF j (TotalHOf.of K _ 2 h) = 0)
    (hnat : ∀ (i : ℕ) (x : TotalHOf K (TopCat.of X)),
      PF i (TotalHOf.map K (cmap (Bundle.flagProj E r)) x)
        = TotalHOf.map K (cmap (Bundle.flagProj E r)) (PN i x)) :
    ParityP.HasSplittingP p D.chern (fun i => Gen.evenRestrictAdd (PN i) (hPN i)) m :=
  hasSplittingP_of_splitRelation D D' (cmap (Bundle.flagProj E r))
    (cmap (Bundle.projComap (Bundle.flagProj E r) E))
    (by rw [hD, hD']; exact flag_square E r) htaut
    (flagProj_map_injective_of_proj E r hstage) r hDr hD'r root hrel
    PN hPN PF hPF hzero hcartan m hone hhigh hnat

end

end ChernSplittingOf

end GroupApproximation.CharClass
