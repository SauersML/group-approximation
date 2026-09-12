import GroupApproximation.CharClass.ChernSplittingOfCompact
import GroupApproximation.CharClass.OddPTotalInterface

/-!
# The splitting principle over `F_p`, from the named reduced powers

Lane `lx-splitK`, prefix `CharClass/ChernSplittingOf*`.

`ChernSplittingOf.hasSplittingPN_of_compact` takes the reduced powers on the flag space as seven
hypotheses about the roots and `1`, plus naturality at the Chern classes.  The named interface
`OddPTotal.EvenReducedPowers p` (lane `lx-pzero`, v3) gives the seven, for every space:

* `P⁰` on the roots — the roots are Euler classes of lines, so they are pullbacks of a class of
  `H²(ℂP^M)`, and `zero_cp` with `natural` gives `P⁰ e(L) = e(L)`;
* `P⁰ 1 = 1` — `zero_one`;
* `Pⁿ 1 = 0` for `n > 0` — `unstable` in degree `0`;
* the Cartan formula on a root times a product of roots — `cartan`, the roots being junk-free
  (`good_two`) and the junk-free classes a subring;
* `P¹ y = y^p` on the roots — `degree_two`, so the normalisation constant is `1`;
* `P^{≥2} y = 0` on the roots — `unstable` in degree `2`.

Naturality at the Chern classes stays a hypothesis for an arbitrary operation `PN` on the base, and
is `natural` itself when `PN` is `ops.P` of the base.

## Main declarations

* `ChernSplittingOf.evenTautOf_pull`, `ChernSplittingOf.zero_pull_cpOps`.
* `ChernSplittingOf.hasSplittingPN_of_compactOps` — `HasSplittingPN` over `F_p` for any `PN`
  intertwined with the reduced powers at the Chern classes.
* `ChernSplittingOf.hasSplittingPN_of_compactOps_self` — the same with `PN := ops.P` of the base.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace ChernSplittingOf

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.LH

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `1` in the even part is the degree-zero class `1`. -/
theorem one_eq_evenOf_one (p : ℕ) (Y : TopCat.{0}) :
    (1 : Gen.evenPart (ZMod p) Y) = OddPTotal.evenOf (ZMod p) Y Even.zero (one (K := ZMod p) Y) :=
  Subtype.ext (TotalHOf.of_one (ZMod p) Y).symm

/-- A pulled-back degree-two class, in the even part, is the pullback of the class. -/
theorem evenTautOf_pull (p : ℕ) {Z Y : TopCat.{0}} (g : Z ⟶ Y) (c : Hmod (ZMod p) Y 2) :
    evenTautOf (ZMod p) (pull g 2 c)
      = Gen.evenMap (ZMod p) g (OddPTotal.evenOf (ZMod p) Y even_two c) :=
  Subtype.ext (TotalHOf.map_of (ZMod p) g 2 c).symm

/-- **`P⁰` fixes every pullback of a degree-two class of a projective space**, in particular every
Euler class of a line bundle. -/
theorem zero_pull_cpOps (p : ℕ) (ops : OddPTotal.EvenReducedPowers p) {Z : TopCat.{0}} (M : ℕ)
    (g : Z ⟶ CPtop M) (c : Hmod (ZMod p) (CPtop M) 2) :
    ops.P Z 0 (evenTautOf (ZMod p) (pull g 2 c)) = evenTautOf (ZMod p) (pull g 2 c) := by
  rw [evenTautOf_pull, ops.natural, ops.zero_cp]

/-- **The splitting principle over `F_p`**, for a bundle of constant positive rank over a compact
non-empty base, from compact Leray–Hirsch over `F_p`, the reduced powers on the flag space, and any
operation `PN` on the base intertwined with them at the Chern classes.  The normalisation constant
is `1`. -/
theorem hasSplittingPN_of_compactOps (p : ℕ) [Fact p.Prime]
    (hgen : Hmod (ZMod p) (CPtop (1 + tautCardOf ι)) 2)
    (hLH : CompactLerayHirschDualOf (ZMod p) ι hgen) (ops : OddPTotal.EvenReducedPowers p)
    [CompactSpace X] [Nonempty X] (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (hrank : ∀ x, E.rank x = r)
    (PN : ℕ → Gen.evenPart (ZMod p) (TopCat.of X) →+ Gen.evenPart (ZMod p) (TopCat.of X))
    (hnat : ∀ i : ℕ,
      ops.P (TopCat.of (Bundle.Flag E r)) i (Gen.evenMap (ZMod p) (cmap (Bundle.flagProj E r))
          ((LerayHirschDataEvenOf.of_graded (hLH X E r hrank hr1)).chern (i + 1)))
        = Gen.evenMap (ZMod p) (cmap (Bundle.flagProj E r))
            (PN i ((LerayHirschDataEvenOf.of_graded (hLH X E r hrank hr1)).chern (i + 1)))) :
    ParityP.HasSplittingPN p (LerayHirschDataEvenOf.of_graded (hLH X E r hrank hr1)).chern PN 1 := by
  refine hasSplittingPN_of_compact (ZMod p) hgen hLH E r hr1 hrank PN
    (ops.P (TopCat.of (Bundle.Flag E r)))
    (fun l => zero_pull_cpOps p ops (1 + tautCardOf ι) _ hgen) (ops.zero_one _) ?_ ?_ 1 ?_ ?_
    hnat
  · intro n hn
    rw [one_eq_evenOf_one p (TopCat.of (Bundle.Flag E r))]
    exact ops.unstable _ n Even.zero (one (K := ZMod p) _) (by omega)
  · intro n l C
    exact ops.cartan _ n _ _ (ops.good_two _ (flagRootOf (ZMod p) hgen E r hr1 l))
      (Subring.prod_mem _ fun l' _ => ops.good_two _ (flagRootOf (ZMod p) hgen E r hr1 l'))
  · intro l
    rw [Int.cast_one, one_mul]
    exact ops.degree_two _ (flagRootOf (ZMod p) hgen E r hr1 l)
  · intro l j hj
    exact ops.unstable _ j even_two (flagRootOf (ZMod p) hgen E r hr1 l) (by omega)

/-- **The splitting principle over `F_p`, with the reduced powers of the base**: `PN := ops.P` of
the base, naturality being the interface's own. -/
theorem hasSplittingPN_of_compactOps_self (p : ℕ) [Fact p.Prime]
    (hgen : Hmod (ZMod p) (CPtop (1 + tautCardOf ι)) 2)
    (hLH : CompactLerayHirschDualOf (ZMod p) ι hgen) (ops : OddPTotal.EvenReducedPowers p)
    [CompactSpace X] [Nonempty X] (E : Bundle X ι) (r : ℕ) (hr1 : 1 ≤ r)
    (hrank : ∀ x, E.rank x = r) :
    ParityP.HasSplittingPN p (LerayHirschDataEvenOf.of_graded (hLH X E r hrank hr1)).chern
      (ops.P (TopCat.of X)) 1 :=
  hasSplittingPN_of_compactOps p hgen hLH ops E r hr1 hrank (ops.P (TopCat.of X))
    (fun i => ops.natural (cmap (Bundle.flagProj E r)) i _)

end

#audit_axioms one_eq_evenOf_one
#audit_axioms evenTautOf_pull
#audit_axioms zero_pull_cpOps
#audit_axioms hasSplittingPN_of_compactOps
#audit_axioms hasSplittingPN_of_compactOps_self

end ChernSplittingOf
end CharClass
end GroupApproximation
