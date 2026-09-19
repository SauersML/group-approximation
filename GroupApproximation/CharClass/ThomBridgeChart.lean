import GroupApproximation.CharClass.RelativeExcision
import GroupApproximation.CharClass.RelativeLocal
import GroupApproximation.CharClass.BundleChartTotal
import GroupApproximation.CharClass.GysinCover

/-!
# The Thom bridge, steps one and two: down to the total space

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

The Thom class from Leray–Hirsch lives on the **projectivisation**; the section
of `cc-lix-odd`'s chain lives on the **vector-bundle total space**.  Both sides
were green and about different objects — a mismatch no probe can see, found only
by comparing statements.  This file is the first half of the bridge:

```text
H^n(P(p⊕1), P(p⊕1) ∖ Z)  ≅  H^n(chart, chart ∖ Z)  ≅  H^n(E, E ∖ 0).
```

Step one is excision along the cover of `P(p⊕1)` by the affine chart and the
complement of the zero section.  **The order matters**: excision quotients by the
*first* open and lands on the *second*, so the not-zero opens are `U` and the
chart is `V`.  `Gysin.chartOpens_sup_notZeroOpens` is stated the other way round,
and `sup_comm` is the whole difference.

Step two is `cc-bundle`'s `chartOpensHomeoTotal`, the chart *is* the total space,
transported by `relCohomologyCongr`.  What makes it a map of **pairs** is their
`chartOpensHomeoTotal_mem_puncturedSet`, an iff in both directions, from which
the image equation below follows.

## Main declarations

* `chartExcisedImage` — the homeomorphism carries the excised subspace onto the
  complement of the zero section in the total space.
* `bridgeChart` — steps one and two composed.
-/

open CategoryTheory TopologicalSpace

namespace GroupApproximation.CharClass

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The chart-to-total homeomorphism is a map of pairs: it carries the part of the
chart off the zero section onto the complement of the zero section in the total
space.  Both directions come from `cc-bundle`'s membership iff. -/
theorem chartExcisedImage (p : Bundle X ι) :
    (Bundle.chartOpensHomeoTotal p) ''
        {z : ↥(Bundle.chartOpensSet p) |
          (z : Bundle.Proj p.plusOne) ∈ Bundle.notZeroOpensSet p}
      = (Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Bundle.chartOpensHomeoTotal_mem_puncturedSet p z).mpr hz
  · intro hw
    refine ⟨(Bundle.chartOpensHomeoTotal p).symm w, ?_,
      (Bundle.chartOpensHomeoTotal p).apply_symm_apply w⟩
    refine (Bundle.chartOpensHomeoTotal_mem_puncturedSet p _).mp ?_
    rw [(Bundle.chartOpensHomeoTotal p).apply_symm_apply]
    exact hw

/-- **Steps one and two of the Thom bridge.**  Excision to the affine chart, then
the chart identified with the total space. -/
def bridgeChart (p : Bundle X ι) (n : ℕ) :
    relCohomology (ZMod 2) (TopCat.of (Bundle.Proj p.plusOne))
        ((Gysin.notZeroOpens p : Opens (TopCat.of (Bundle.Proj p.plusOne)))
          : Set (Bundle.Proj p.plusOne)) n
      ≅ relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
        ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p) n :=
  (excisionIso (Gysin.notZeroOpens p) (Gysin.chartOpens p)
      (by rw [sup_comm]; exact Gysin.chartOpens_sup_notZeroOpens p) n).trans
    (relCohomologyCongr (Bundle.chartOpensHomeoTotal p) _ _ (chartExcisedImage p) n)

end

end GroupApproximation.CharClass
