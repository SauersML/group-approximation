import GroupApproximation.CharClass.ChernSplittingOfFlagRelation
import GroupApproximation.CharClass.ParityPSplitStepDNarrow
import GroupApproximation.CharClass.CohomologyTotalNontrivialOf

/-!
# The splitting principle over `K`, narrowed, for a bundle over a compact base

Lane `lx-splitK`, prefix `CharClass/ChernSplittingOf*`, ruling of `lx-design` 2026-09-12.

The producer of `ParityP.HasSplittingPN` (`ParityPSplitStepDNarrow`) for the Chern classes of a
bundle of constant positive rank over a compact non-empty base, over a field `K`.  Compared with
`hasSplittingP_flag`:

* the reduced powers are additive maps on the **even parts**, the carrier of every consumer;
* `P⁰` is asked on the roots and on `1` only, `Pⁿ 1 = 0` for `n > 0`, the Cartan formula for a root
  times a product of roots, `P¹ y = m·y^p` and `P^{≥2} y = 0` on the roots;
* naturality along the flag projection is asked only at the Chern classes `γ (i+1)`.

The roots are the Euler classes over `K` of the tautological lines of the flag,
`ChernSplittingOf.flagRootOf`.  The geometry is discharged: the split relation
(`ChernSplittingOfFlagRelation`), injectivity along the tower from compact Leray–Hirsch
(`flagRest_pull_injectiveOf`), and compactness and non-emptiness of the flag.  What stays a
hypothesis is one named Leray–Hirsch input, `CompactLerayHirschDualOf`, and the reduced powers.

## Main declarations

* `SplittingDataOf.powerDataN`, `hasSplittingPN_of_splittingDataOf` — the producer on even parts.
* `nontrivial_evenPartOf_of_nonempty` — the even part of a nonempty space is nontrivial.
* `ChernSplittingOf.flagRootOf` — the roots at the flag.
* `ChernSplittingOf.hasSplittingPN_flag_ofGraded` — the flag assembly.
* `ChernSplittingOf.CompactLerayHirschDualOf` — the named Leray–Hirsch input.
* `ChernSplittingOf.flagRest_pull_injectiveOf` — injectivity at every stage of the tower.
* `ChernSplittingOf.hasSplittingPN_of_compact` — **the splitting principle over `K`** for a bundle
  over a compact non-empty base.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH

noncomputable section

/-! ## 1. The producer on even parts -/

namespace SplittingDataOf

variable {K : Type} [CommRing K] {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → Gen.evenPart K N}
  (S : SplittingDataOf K N F r γ)

/-- **The narrowed `PowerData` of the roots**, from reduced powers on the even part of `F`. -/
def powerDataN {p : ℕ} (PF : ℕ → Gen.evenPart K F →+ Gen.evenPart K F)
    (hzero_root : ∀ l : ℕ, PF 0 (S.evenRoot l) = S.evenRoot l)
    (hzero_one : PF 0 1 = 1)
    (hone_pos : ∀ n : ℕ, 0 < n → PF n 1 = 0)
    (hcartan : ∀ (n l : ℕ) (C : Finset ℕ),
      PF n (S.evenRoot l * ∏ l' ∈ C, S.evenRoot l')
        = ∑ j ∈ Finset.range (n + 1), PF j (S.evenRoot l) * PF (n - j) (∏ l' ∈ C, S.evenRoot l'))
    (m : ℤ)
    (hone : ∀ l : ℕ, PF 1 (S.evenRoot l) = (m : Gen.evenPart K F) * S.evenRoot l ^ p)
    (hhigh : ∀ (l j : ℕ), 2 ≤ j → PF j (S.evenRoot l) = 0) :
    ParityP.PowerDataN ℕ (Gen.evenPart K F) p where
  P := PF
  s := Finset.range r
  y := S.evenRoot
  κ := (m : Gen.evenPart K F)
  p_zero_y := hzero_root
  p_zero_one := hzero_one
  p_one_pos := hone_pos
  cartan_y := hcartan
  p_y_one := hone
  p_y_high := hhigh

end SplittingDataOf

/-- **The narrowed producer of the splitting principle**, from splitting data and reduced powers on
even parts. -/
theorem hasSplittingPN_of_splittingDataOf {K : Type} [CommRing K] {p : ℕ} {N F : TopCat.{0}}
    {r : ℕ} {γ : ℕ → Gen.evenPart K N} (S : SplittingDataOf K N F r γ)
    (PN : ℕ → Gen.evenPart K N →+ Gen.evenPart K N)
    (PF : ℕ → Gen.evenPart K F →+ Gen.evenPart K F)
    (hzero_root : ∀ l : ℕ, PF 0 (S.evenRoot l) = S.evenRoot l)
    (hzero_one : PF 0 1 = 1)
    (hone_pos : ∀ n : ℕ, 0 < n → PF n 1 = 0)
    (hcartan : ∀ (n l : ℕ) (C : Finset ℕ),
      PF n (S.evenRoot l * ∏ l' ∈ C, S.evenRoot l')
        = ∑ j ∈ Finset.range (n + 1), PF j (S.evenRoot l) * PF (n - j) (∏ l' ∈ C, S.evenRoot l'))
    (m : ℤ)
    (hone : ∀ l : ℕ, PF 1 (S.evenRoot l) = (m : Gen.evenPart K F) * S.evenRoot l ^ p)
    (hhigh : ∀ (l j : ℕ), 2 ≤ j → PF j (S.evenRoot l) = 0)
    (hnat : ∀ i : ℕ,
      PF i (Gen.evenMap K S.proj (γ (i + 1))) = Gen.evenMap K S.proj (PN i (γ (i + 1)))) :
    ParityP.HasSplittingPN p γ PN m := by
  refine ⟨Gen.evenPart K F, inferInstance, ℕ, inferInstance,
    S.powerDataN PF hzero_root hzero_one hone_pos hcartan m hone hhigh, Gen.evenMap K S.proj,
    ?_, ?_, ?_, rfl⟩
  · intro a b hab
    exact Subtype.ext (S.pull_injective (congrArg Subtype.val hab))
  · intro k
    exact S.chern_split k
  · intro i
    exact (hnat i).symm

/-- **The even part of a nonempty space is nontrivial**, over every nontrivial ring. -/
theorem nontrivial_evenPartOf_of_nonempty (K : Type) [CommRing K] [Nontrivial K] (Y : TopCat.{0})
    [Nonempty Y] : Nontrivial (Gen.evenPart K Y) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h' : (1 : TotalHOf K Y) = 0 := congrArg Subtype.val h
  exact one_ne_zero h'

namespace ChernSplittingOf

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 2. The flag assembly -/

/-- **The roots at the flag**: the Euler classes over `K` of the tautological lines of the top
stage of the flag tower. -/
def flagRootOf (K : Type) [CommRing K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r) (l : ℕ) : Hmod K (TopCat.of (Bundle.Flag E r)) 2 :=
  lineEulerOfK K hgen (Wu.flagLineFlat E r l) (Wu.trace_flagLineFlat E r hr1 l)

/-- **The flag assembly over a field, narrowed.**  Leray–Hirsch data for `E` and for its pullback
to the flag, injectivity along the tower, and reduced powers on the even parts asked about only on
the roots, on `1`, and at the Chern classes, give `HasSplittingPN` for the Chern classes of `E`. -/
theorem hasSplittingPN_flag_ofGraded (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) {p : ℕ} (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (hrank : ∀ x, E.rank x = r)
    [Nontrivial (Gen.evenPart K (TopCat.of X))]
    [Nontrivial (Gen.evenPart K (TopCat.of (Bundle.Flag E r)))]
    (L : LerayHirschGraded (cmap (Bundle.projPi E)) (LH.tautEulerDualK K hgen E) r)
    (L' : LerayHirschGraded (cmap (Bundle.projPi (Wu.flagPullback E r)))
      (LH.tautEulerDualK K hgen (Wu.flagPullback E r)) r)
    (hstage : ∀ n : ℕ, n < r → ∀ k : ℕ,
      Function.Injective (pull (K := K) (cmap (Bundle.projPi (Bundle.flagRest E n))) k))
    (PN : ℕ → Gen.evenPart K (TopCat.of X) →+ Gen.evenPart K (TopCat.of X))
    (PF : ℕ → Gen.evenPart K (TopCat.of (Bundle.Flag E r)) →+
      Gen.evenPart K (TopCat.of (Bundle.Flag E r)))
    (hzero_root : ∀ l : ℕ, PF 0 (evenTautOf K (flagRootOf K hgen E r hr1 l))
      = evenTautOf K (flagRootOf K hgen E r hr1 l))
    (hzero_one : PF 0 1 = 1)
    (hone_pos : ∀ n : ℕ, 0 < n → PF n 1 = 0)
    (hcartan : ∀ (n l : ℕ) (C : Finset ℕ),
      PF n (evenTautOf K (flagRootOf K hgen E r hr1 l)
          * ∏ l' ∈ C, evenTautOf K (flagRootOf K hgen E r hr1 l'))
        = ∑ j ∈ Finset.range (n + 1), PF j (evenTautOf K (flagRootOf K hgen E r hr1 l))
            * PF (n - j) (∏ l' ∈ C, evenTautOf K (flagRootOf K hgen E r hr1 l')))
    (m : ℤ)
    (hone : ∀ l : ℕ, PF 1 (evenTautOf K (flagRootOf K hgen E r hr1 l))
      = (m : Gen.evenPart K (TopCat.of (Bundle.Flag E r)))
          * evenTautOf K (flagRootOf K hgen E r hr1 l) ^ p)
    (hhigh : ∀ (l j : ℕ), 2 ≤ j → PF j (evenTautOf K (flagRootOf K hgen E r hr1 l)) = 0)
    (hnat : ∀ i : ℕ,
      PF i (Gen.evenMap K (cmap (Bundle.flagProj E r))
          ((LerayHirschDataEvenOf.of_graded L).chern (i + 1)))
        = Gen.evenMap K (cmap (Bundle.flagProj E r))
            (PN i ((LerayHirschDataEvenOf.of_graded L).chern (i + 1)))) :
    ParityP.HasSplittingPN p (LerayHirschDataEvenOf.of_graded L).chern PN m :=
  hasSplittingPN_of_splittingDataOf
    (splittingDataOf_of_splitPoly (LerayHirschDataEvenOf.of_graded L)
      (cmap (Bundle.flagProj E r)) (flagProj_map_injective_of_proj E r hstage) r rfl
      (flagRootOf K hgen E r hr1)
      (splitPoly_of_splitRelation (LerayHirschDataEvenOf.of_graded L)
        (LerayHirschDataEvenOf.of_graded L') (cmap (Bundle.flagProj E r))
        (cmap (Bundle.projComap (Bundle.flagProj E r) E)) (flag_square E r)
        (tautCompat_flagOf K hgen E r) r rfl rfl (flagRootOf K hgen E r hr1)
        (splitRelation_flagOf K hgen E r hr1 hrank)))
    PN PF hzero_root hzero_one hone_pos hcartan m hone hhigh hnat

/-! ## 3. The named Leray–Hirsch input, and injectivity along the tower -/

/-- **Compact Leray–Hirsch over `K`, with the dual tautological class.**  For every bundle of
constant positive rank `s` over a compact non-empty base, `1, ξ, …, ξ^{s-1}` with
`ξ = LH.tautEulerDualK K hgen q` is a basis of the cohomology of the projectivisation in every
degree.  Producer: lane `lx-lhK-b` (`LH.lerayHirschGraded_compactOf`, dual form, for `hgen ≠ 0`). -/
def CompactLerayHirschDualOf (K : Type) [CommRing K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z] (q : Bundle Z ι) (s : ℕ),
    (∀ z, q.rank z = s) → 1 ≤ s →
      LerayHirschGraded (cmap (Bundle.projPi q)) (LH.tautEulerDualK K hgen q) s

/-- **Injectivity at every stage of the flag tower**, from compact Leray–Hirsch over `K`.  At stage
`n < r` the rest bundle has constant rank `r − n ≥ 1` over a compact non-empty base. -/
theorem flagRest_pull_injectiveOf (K : Type) [CommRing K]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hLH : CompactLerayHirschDualOf K ι hgen)
    [CompactSpace X] [Nonempty X] (E : Bundle X ι) (r : ℕ) (hrank : ∀ x, E.rank x = r) :
    ∀ n : ℕ, n < r → ∀ k : ℕ,
      Function.Injective (pull (K := K) (cmap (Bundle.projPi (Bundle.flagRest E n))) k) := by
  intro n hn k
  haveI := Wu.flag_compactSpace E n
  haveI := Wu.flag_nonempty E r hrank n (by omega)
  exact (hLH (Bundle.Flag E n) (Bundle.flagRest E n) (r - n)
    (fun w => by have h := Wu.flagRest_rank_eq E r hrank n w; omega) (by omega)).pull_injective
    (by omega) k

/-! ## 4. The splitting principle over `K` -/

/-- **The splitting principle over `K`, narrowed**, for a bundle of constant positive rank over a
compact non-empty base, from compact Leray–Hirsch over `K` and reduced powers on the even parts. -/
theorem hasSplittingPN_of_compact (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hLH : CompactLerayHirschDualOf K ι hgen)
    {p : ℕ} [CompactSpace X] [Nonempty X] (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (hrank : ∀ x, E.rank x = r)
    (PN : ℕ → Gen.evenPart K (TopCat.of X) →+ Gen.evenPart K (TopCat.of X))
    (PF : ℕ → Gen.evenPart K (TopCat.of (Bundle.Flag E r)) →+
      Gen.evenPart K (TopCat.of (Bundle.Flag E r)))
    (hzero_root : ∀ l : ℕ, PF 0 (evenTautOf K (flagRootOf K hgen E r hr1 l))
      = evenTautOf K (flagRootOf K hgen E r hr1 l))
    (hzero_one : PF 0 1 = 1)
    (hone_pos : ∀ n : ℕ, 0 < n → PF n 1 = 0)
    (hcartan : ∀ (n l : ℕ) (C : Finset ℕ),
      PF n (evenTautOf K (flagRootOf K hgen E r hr1 l)
          * ∏ l' ∈ C, evenTautOf K (flagRootOf K hgen E r hr1 l'))
        = ∑ j ∈ Finset.range (n + 1), PF j (evenTautOf K (flagRootOf K hgen E r hr1 l))
            * PF (n - j) (∏ l' ∈ C, evenTautOf K (flagRootOf K hgen E r hr1 l')))
    (m : ℤ)
    (hone : ∀ l : ℕ, PF 1 (evenTautOf K (flagRootOf K hgen E r hr1 l))
      = (m : Gen.evenPart K (TopCat.of (Bundle.Flag E r)))
          * evenTautOf K (flagRootOf K hgen E r hr1 l) ^ p)
    (hhigh : ∀ (l j : ℕ), 2 ≤ j → PF j (evenTautOf K (flagRootOf K hgen E r hr1 l)) = 0)
    (hnat : ∀ i : ℕ,
      PF i (Gen.evenMap K (cmap (Bundle.flagProj E r))
          ((LerayHirschDataEvenOf.of_graded (hLH X E r hrank hr1)).chern (i + 1)))
        = Gen.evenMap K (cmap (Bundle.flagProj E r))
            (PN i ((LerayHirschDataEvenOf.of_graded (hLH X E r hrank hr1)).chern (i + 1)))) :
    ParityP.HasSplittingPN p (LerayHirschDataEvenOf.of_graded (hLH X E r hrank hr1)).chern PN m := by
  haveI := Wu.flag_compactSpace E r
  haveI hflag : Nonempty (Bundle.Flag E r) := Wu.flag_nonempty E r hrank r le_rfl
  haveI : Nonempty (TopCat.of X) := ‹Nonempty X›
  haveI : Nonempty (TopCat.of (Bundle.Flag E r)) := hflag
  haveI : Nontrivial (Gen.evenPart K (TopCat.of X)) := nontrivial_evenPartOf_of_nonempty K (TopCat.of X)
  haveI : Nontrivial (Gen.evenPart K (TopCat.of (Bundle.Flag E r))) :=
    nontrivial_evenPartOf_of_nonempty K (TopCat.of (Bundle.Flag E r))
  exact hasSplittingPN_flag_ofGraded K hgen E r hr1 hrank (hLH X E r hrank hr1)
    (hLH (Bundle.Flag E r) (Wu.flagPullback E r) r (Wu.rank_flagPullback E r hrank) hr1)
    (flagRest_pull_injectiveOf K hgen hLH E r hrank) PN PF hzero_root hzero_one hone_pos hcartan
    m hone hhigh hnat

end ChernSplittingOf

end

#audit_axioms SplittingDataOf.powerDataN
#audit_axioms hasSplittingPN_of_splittingDataOf
#audit_axioms nontrivial_evenPartOf_of_nonempty
#audit_axioms ChernSplittingOf.flagRootOf
#audit_axioms ChernSplittingOf.hasSplittingPN_flag_ofGraded
#audit_axioms ChernSplittingOf.CompactLerayHirschDualOf
#audit_axioms ChernSplittingOf.flagRest_pull_injectiveOf
#audit_axioms ChernSplittingOf.hasSplittingPN_of_compact

end CharClass
end GroupApproximation
