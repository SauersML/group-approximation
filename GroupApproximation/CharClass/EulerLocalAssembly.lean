import GroupApproximation.CharClass.EulerLocalNonvanishing
import GroupApproximation.CharClass.EulerLocalChart
import GroupApproximation.CharClass.ThomToolkitInstance

/-!
# Step C assembled against the local model

`EulerLocalNonvanishing.topChernClass_ne_zero` takes the one-dimensionality of the
relative group and the nonvanishing of the relative Euler class as two separate
hypotheses.  In the application both come from the same place: excision to a chart
around the single zero, then a homeomorphism of pairs onto the local model
`(ℂ^r, ℂ^r ∖ 0)`, whose top relative cohomology is a line with a named nonzero
generator (`cc-relative`, need (B6)).

This file chains those two steps once, so that instantiating Step C is a single
application rather than a diagram chase:

* `rankOneOfIsoChain` composes the excision isomorphism with the chart isomorphism and
  the local model's one-dimensionality;
* `su_ne_zero_of_chain` transports nonvanishing back along the same two isomorphisms;
* `topChernClass_ne_zero_of_chain` puts them into `topChernClass_ne_zero`.

Nothing here is new mathematics.  It exists so that `cc-lix-odd` and the lead have one
statement to discharge rather than five, and so that the shape of what `cc-relative`
owes is visible in Lean rather than only in prose.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- One-dimensionality of `H^{2r}(N, N ∖ z)` transported from the local model along
excision and the chart. -/
def rankOneOfIsoChain {rel chart loc : ModuleCat.{0} (ZMod 2)}
    (exc : rel ≅ chart) (chartIso : chart ≅ loc) (locEquiv : loc ≃ₗ[ZMod 2] ZMod 2) :
    rel ≃ₗ[ZMod 2] ZMod 2 :=
  rankOneOfIso (exc ≪≫ chartIso) locEquiv

/-- Nonvanishing of the relative Euler class, transported back from the local
generator along the same two isomorphisms. -/
theorem su_ne_zero_of_chain {rel chart loc : ModuleCat.{0} (ZMod 2)}
    (exc : rel ≅ chart) (chartIso : chart ≅ loc) {su : rel} {g : loc}
    (hsu : (exc ≪≫ chartIso).hom.hom su = g) (hg : g ≠ 0) : su ≠ 0 :=
  ne_zero_of_map_ne_zero (exc ≪≫ chartIso).hom (by rw [hsu]; exact hg)

/-- **Step C, in one application.**  A rank-`r` bundle over `N` whose section has `z` as
its only zero, and which is a local homeomorphism there, has nonzero top mod-2 Chern
class.

The hypotheses are exactly what the other lanes owe: `hacyclic` from the
punctured-product recursion (unconditional now, via `cohomologyToolkit`), `j`/`i`/`hexact`
from `cc-relative`'s long exact sequence, `exc` from their excision, `chartIso` from
their homeomorphism invariance of pairs applied to
`EulerLocalChart.openPartialHomeomorphChartPair`, `locEquiv`/`hg` from their local
model, and `hgamma` from the Thom-class construction. -/
theorem topChernClass_ne_zero_of_chain (hacyclic : PuncturedAcyclic N twoR z)
    {rel chart loc : ModuleCat.{0} (ZMod 2)}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (absEquiv : cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2)
    (exc : rel ≅ chart) (chartIso : chart ≅ loc) (locEquiv : loc ≃ₗ[ZMod 2] ZMod 2)
    {su : rel} {g : loc} (hsu : (exc ≪≫ chartIso).hom.hom su = g) (hg : g ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 := by
  refine topChernClass_ne_zero hacyclic j i hexact
    (rankOneOfIsoChain exc chartIso locEquiv) absEquiv (exc ≪≫ chartIso).hom
    (su := su) (g := g) hsu hg hgamma

end

end GroupApproximation.CharClass
