import GroupApproximation.CharClass.ChernSplittingOfFlag
import GroupApproximation.CharClass.ChernEulerIsoOf
import GroupApproximation.CharClass.LerayHirschChartClassGenK
import GroupApproximation.CharClass.CupVanishIterateOf
import GroupApproximation.CharClass.CohomologyLHRingDataOf
import GroupApproximation.CharClass.ParityEvenFlagRelation
import GroupApproximation.Meta.AxiomGuard

/-!
# The splitting principle over `K`: the split relation at the flag

Lane `lx-splitK` (successor of `lix-evenside`), prefix `CharClass/ChernSplittingOf*`.

`ChernSplittingOf.hasSplittingP_flag` takes the split relation on the pulled-back
projectivisation as a hypothesis.  This file proves that relation for a bundle that is a sum of
lines, over a field `K`, and feeds it back together with the even-part Leray–Hirsch data built
from `LerayHirschGraded`.

The geometry is the `F₂` geometry of `ChernSplitFactor`, `ChernSplitRelation` and
`ParityEvenFlagRelation`, with two changes.

* **The sign.**  Over `F₂` each factor `ξ + π^*e(L_l)` vanishes on its open set because a class
  plus itself is zero.  Over `K` the factor is written with `ξ = LH.tautEulerDualK = −e(taut)`.
  On the open set where the tautological line is the summand it reads `−a + a`, which is zero by
  `neg_add_cancel`.
* **The product.**  `TotalHOf K X` is only a graded ring, so vanishing over the cover is stated
  for an ordered `List` product (`prod_eq_zero_of_coverOf`).  `coe_prod_range_evenPart` moves it
  into the commutative even part.

## Main declarations

* `lineEulerOfK` — the Euler class over `K` of a line bundle, at the index of `LH.tautEulerOfK`.
* `eulerOf_restrict_eqOf` — on its open set, the tautological line and the summand have the same
  Euler class.
* `pull_factor_eq_zeroOf` — each factor vanishes on its own open set.
* `coe_prod_range_evenPart` — a finite product in the even part is the ordered product in the
  ring.
* `splitRelation_of_sumOf` — **the split relation** for a sum of lines.
* `ChernSplittingOf.splitRelation_flagOf` — the split relation at the flag.
* `ChernSplittingOf.tautCompat_flagOf` — the tautological classes agree along `projComap`.
* `ChernSplittingOf.hasSplittingP_flag_ofGraded` — `hasSplittingP_flag`, with the Leray–Hirsch
  data, the tautological compatibility and the split relation discharged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The Euler class of a line, over `K` -/

/-- **The Euler class over `K` of a line bundle**, taken at the index of `LH.tautEulerOfK` and
relative to the chosen class `hgen`, so that the two can be compared without reindexing. -/
def lineEulerOfK (K : Type) [CommRing K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) : Hmod K (TopCat.of X) 2 :=
  eulerOfBundleOf K hgen (Bundle.pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q)
    (CPn.trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) q hq)

/-- **On `lineOpenSet p q` the two Euler classes agree**, over a field.  The bundles are
isomorphic there (`Bundle.tautLineIsoSummand`), and the Euler class over `K` is an isomorphism
invariant for every `hgen` (`CPn.eulerOfBundle_eq_of_bundleIsoOf`). -/
theorem eulerOf_restrict_eqOf (K : Type) [Field K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (p q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    lineEulerOfK K hgen (Bundle.restrictTo (Bundle.tautLine p) (Bundle.lineOpenSet p q))
        (fun y => Bundle.trace_tautLine p (y : Bundle.Proj p))
      = lineEulerOfK K hgen
          (Bundle.restrictTo (Bundle.comap (Bundle.projPi p) q) (Bundle.lineOpenSet p q))
          (fun y => hq (Bundle.projPi p (y : Bundle.Proj p))) :=
  CPn.eulerOfBundle_eq_of_bundleIsoOf K (show 1 ≤ 1 + tautCardOf ι by omega) hgen _ _ _ _
    (pushforwardBundleIso (tautEmbOf ι) (tautEmbOf_injective ι)
      (Bundle.tautLineIsoSummand p q hq))

/-! ## 2. Each factor vanishes on its open set -/

/-- **Each factor vanishes on its own open set**, over a field.  There `ξ = −e(taut)` and
`π^* e(L)` restrict to `−a` and `a` for the same class `a`. -/
theorem pull_factor_eq_zeroOf (K : Type) [Field K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (p q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    pull (opIncl (lineOpens p q)) 2
        (LH.tautEulerDualK K hgen p + pull (cmap (Bundle.projPi p)) 2 (lineEulerOfK K hgen q hq))
      = 0 := by
  have h1 : pull (opIncl (lineOpens p q)) 2 (LH.tautEulerOfK K hgen p)
      = lineEulerOfK K hgen (Bundle.restrictTo (Bundle.tautLine p) (Bundle.lineOpenSet p q))
          (fun y => Bundle.trace_tautLine p (y : Bundle.Proj p)) :=
    (eulerOfBundle_comapOf K hgen
      (Bundle.pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (Bundle.tautLine p)) _
      ⟨Subtype.val, continuous_subtype_val⟩).symm
  have h2 : pull (opIncl (lineOpens p q)) 2
        (pull (cmap (Bundle.projPi p)) 2 (lineEulerOfK K hgen q hq))
      = lineEulerOfK K hgen
          (Bundle.restrictTo (Bundle.comap (Bundle.projPi p) q) (Bundle.lineOpenSet p q))
          (fun y => hq (Bundle.projPi p (y : Bundle.Proj p))) := by
    rw [← pull_comp]
    exact (eulerOfBundle_comapOf K hgen
      (Bundle.pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q) _
      ((Bundle.projPi p).comp ⟨Subtype.val, continuous_subtype_val⟩)).symm
  have hneg : pull (opIncl (lineOpens p q)) 2 (-LH.tautEulerOfK K hgen p)
      = -pull (opIncl (lineOpens p q)) 2 (LH.tautEulerOfK K hgen p) :=
    map_neg (pullLinear (K := K) (opIncl (lineOpens p q)) 2) (LH.tautEulerOfK K hgen p)
  rw [pull_add, LH.tautEulerDualK, hneg, h1, h2, eulerOf_restrict_eqOf K hgen p q hq,
    neg_add_cancel]

/-! ## 3. Products in the even part -/

/-- **A finite product in the even part is the ordered product in the ring.**  The even part is
commutative and `TotalHOf K Y` is not, so the ring side is a `List` product. -/
theorem coe_prod_range_evenPart {K : Type} [CommRing K] {Y : TopCat.{0}}
    (f : ℕ → Gen.evenPart K Y) (g : ℕ → TotalHOf K Y)
    (hfg : ∀ l, (f l : TotalHOf K Y) = g l) (r : ℕ) :
    ((∏ l ∈ Finset.range r, f l : Gen.evenPart K Y) : TotalHOf K Y)
      = ((List.range r).map g).prod := by
  induction r with
  | zero => exact congrArg Subtype.val (Finset.prod_range_zero f)
  | succ r ih =>
    calc ((∏ l ∈ Finset.range (r + 1), f l : Gen.evenPart K Y) : TotalHOf K Y)
        = ((∏ l ∈ Finset.range r, f l : Gen.evenPart K Y) : TotalHOf K Y)
            * (f r : TotalHOf K Y) :=
          congrArg Subtype.val (Finset.prod_range_succ f r)
      _ = ((List.range r).map g).prod * g r := by rw [ih, hfg r]
      _ = ((List.range (r + 1)).map g).prod := (List.prod_range_succ g r).symm

/-! ## 4. The split relation -/

/-- **The split relation over a field, for a bundle that is a sum of lines.**  The roots are the
Euler classes of the summands and the tautological class is `ξ = LH.tautEulerDualK`. -/
theorem splitRelation_of_sumOf (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (p : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (qf : ℕ → Bundle X ι) (hq : ∀ l x, (qf l x).trace = 1)
    (hsum : ∀ x, p x = ∑ l ∈ Finset.range r, qf l x) :
    ∏ l ∈ Finset.range r,
      (evenTautOf K (LH.tautEulerDualK K hgen p)
        + Gen.evenMap K (cmap (Bundle.projPi p))
            (evenTautOf K (lineEulerOfK K hgen (qf l) (hq l)))) = 0 := by
  apply Subtype.ext
  refine (coe_prod_range_evenPart _
    (fun l => TotalHOf.of K (TopCat.of (Bundle.Proj p)) 2
      (LH.tautEulerDualK K hgen p
        + pull (cmap (Bundle.projPi p)) 2 (lineEulerOfK K hgen (qf l) (hq l)))) ?_ r).trans ?_
  · intro l
    show TotalHOf.of K (TopCat.of (Bundle.Proj p)) 2 (LH.tautEulerDualK K hgen p)
        + TotalHOf.map K (cmap (Bundle.projPi p))
            (TotalHOf.of K (TopCat.of X) 2 (lineEulerOfK K hgen (qf l) (hq l))) = _
    rw [TotalHOf.map_of]
    exact (map_add (TotalHOf.of K (TopCat.of (Bundle.Proj p)) 2) _ _).symm
  · exact prod_eq_zero_of_coverOf K (fun l => lineOpens p (qf l)) r (by omega)
      (coverSup_lineOpens p r qf hsum) 2 (by omega) _
      (fun l => pull_factor_eq_zeroOf K hgen p (qf l) (hq l))

namespace ChernSplittingOf

/-- **The split relation at the flag**, over a field: on the top stage of the flag tower the
pullback of the bundle is the sum of the tautological lines (`Wu.sum_flagLineFlat`). -/
theorem splitRelation_flagOf (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (hrank : ∀ x, E.rank x = r) :
    ∏ l ∈ Finset.range r,
      (evenTautOf K (LH.tautEulerDualK K hgen (Wu.flagPullback E r))
        + Gen.evenMap K (cmap (Bundle.projPi (Wu.flagPullback E r)))
            (evenTautOf K (lineEulerOfK K hgen (Wu.flagLineFlat E r l)
              (Wu.trace_flagLineFlat E r hr1 l)))) = 0 :=
  splitRelation_of_sumOf K hgen (Wu.flagPullback E r) r hr1 (Wu.flagLineFlat E r)
    (fun l => Wu.trace_flagLineFlat E r hr1 l) (Wu.sum_flagLineFlat E r hrank)

/-- **The tautological classes agree along `projComap`**, over any ring and for every `hgen`. -/
theorem tautCompat_flagOf (K : Type) [CommRing K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (E : Bundle X ι) (r : ℕ) :
    TotalHOf.of K (TopCat.of (Bundle.Proj (Bundle.comap (Bundle.flagProj E r) E))) 2
        (LH.tautEulerDualK K hgen (Bundle.comap (Bundle.flagProj E r) E))
      = TotalHOf.map K (cmap (Bundle.projComap (Bundle.flagProj E r) E))
          (TotalHOf.of K (TopCat.of (Bundle.Proj E)) 2 (LH.tautEulerDualK K hgen E)) := by
  rw [TotalHOf.map_of, LH.tautEulerDual_comapOf]

/-- **`hasSplittingP_flag` with its geometric inputs discharged.**  The even-part Leray–Hirsch
data come from `LerayHirschGraded` for `E` and for its pullback to the flag, both with the dual
tautological class; the compatibility of the tautological classes and the split relation are
theorems.  What stays a hypothesis is the Leray–Hirsch injectivity at each stage of the tower
and the reduced powers. -/
theorem hasSplittingP_flag_ofGraded (K : Type) [Field K]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) {p : ℕ} (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (hrank : ∀ x, E.rank x = r)
    [Nontrivial (Gen.evenPart K (TopCat.of X))]
    [Nontrivial (Gen.evenPart K (TopCat.of (Bundle.Flag E r)))]
    (L : LerayHirschGraded (cmap (Bundle.projPi E)) (LH.tautEulerDualK K hgen E) r)
    (L' : LerayHirschGraded (cmap (Bundle.projPi (Wu.flagPullback E r)))
      (LH.tautEulerDualK K hgen (Wu.flagPullback E r)) r)
    (hstage : ∀ n : ℕ, n < r → ∀ k : ℕ,
      Function.Injective (pull (K := K) (cmap (Bundle.projPi (Bundle.flagRest E n))) k))
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
    ParityP.HasSplittingP p (LerayHirschDataEvenOf.of_graded L).chern
      (fun i => Gen.evenRestrictAdd (PN i) (hPN i)) m :=
  hasSplittingP_flag E r (LerayHirschDataEvenOf.of_graded L) rfl rfl
    (LerayHirschDataEvenOf.of_graded L') rfl rfl (tautCompat_flagOf K hgen E r) hstage
    (fun l => lineEulerOfK K hgen (Wu.flagLineFlat E r l) (Wu.trace_flagLineFlat E r hr1 l))
    (splitRelation_flagOf K hgen E r hr1 hrank) PN hPN PF hPF hzero hcartan m hone hhigh hnat

end ChernSplittingOf

end

#audit_axioms lineEulerOfK
#audit_axioms eulerOf_restrict_eqOf
#audit_axioms pull_factor_eq_zeroOf
#audit_axioms coe_prod_range_evenPart
#audit_axioms splitRelation_of_sumOf
#audit_axioms ChernSplittingOf.splitRelation_flagOf
#audit_axioms ChernSplittingOf.tautCompat_flagOf
#audit_axioms ChernSplittingOf.hasSplittingP_flag_ofGraded

end CharClass
end GroupApproximation
