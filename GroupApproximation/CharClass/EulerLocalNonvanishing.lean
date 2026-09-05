import GroupApproximation.CharClass.ThomFieldTwo
import GroupApproximation.CharClass.ThomPuncturedRecursion

/-!
# Step C assembled: one zero, a local homeomorphism there, so `γ_r ≠ 0`

This file states and proves the conclusion of Step C of the LIX obstruction
(`notes/LIX_FULL_PROGRAM_2026-09-05.md` §1.3) at the level of the cohomological
interface, i.e. modulo the constructions owned by `cc-relative`, `cc-bundle` and
`cc-projective`.  The argument being assembled is:

1. the section `s` of the rank-`r` bundle `W_g` over `N` has exactly one zero `z`,
   and near `z` it is a homeomorphism onto a neighbourhood of `0` in the fibre;
2. so the relative Euler class `s^* u ∈ H^{2r}(N, N ∖ z; F₂)` excises to the chart
   and, by a *homeomorphism of pairs*, becomes the generator of
   `H^{2r}(ℂ^r, ℂ^r ∖ 0; F₂) ≅ F₂` — **no degree computation**;
3. in particular `s^* u ≠ 0`;
4. `H^{2r}(N ∖ z; F₂) = 0` by the punctured-product recursion, so the long exact
   sequence of the pair makes `j^* : H^{2r}(N, N ∖ z) → H^{2r}(N)` surjective;
5. both sides are one dimensional over `F₂`, so `j^*` is injective;
6. `γ_r(W_g) = j^*(s^* u) ≠ 0`.

Steps 3, 5 and 6 are proved here; steps 1, 2 and 4 enter as hypotheses which name
exactly the peer deliverables (`notes/lix-lane-reports/cc-thom.md` §3).

## Main results

* `ne_zero_of_map_ne_zero` — step 3: nonvanishing pulls back along any linear map, so
  an excision isomorphism carrying `s^* u` to a nonzero local generator proves
  `s^* u ≠ 0`.
* `surjective_of_punctured_acyclic` — step 4.
* `topChernClass_ne_zero` — steps 3–6 in one statement, the form `cc-lix-odd` should
  instantiate.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

section Transport

variable {R : Type*} [Ring R]

/-- **Nonvanishing pulls back.**  If some linear map does not kill `x`, then `x ≠ 0`.

This is the entire content of "the relative Euler class is nonzero": excision to a chart
around the single zero, followed by the homeomorphism of pairs given by the local
homeomorphism at that zero, carries `s^* u` to the generator of
`H^{2r}(ℂ^r, ℂ^r ∖ 0) ≅ F₂`, which is nonzero.  A homeomorphism of pairs induces an
isomorphism, and no degree is ever computed. -/
theorem ne_zero_of_map_ne_zero {M N : ModuleCat.{0} R} (f : M ⟶ N) {x : M}
    (h : f.hom x ≠ 0) : x ≠ 0 := by
  intro hx
  exact h (by rw [hx, map_zero])

end Transport

section StepC

variable {N : Type} [TopologicalSpace N] {twoR : ℕ} {z : N}

/-- **Step 4.**  The punctured-product recursion kills `H^{2r}(N ∖ z; F₂)`, and the long
exact sequence of the pair — exactness at `H^{2r}(N)`, given here as
`range j^* = ker i^*` — then makes `j^*` surjective. -/
theorem surjective_of_punctured_acyclic (hacyclic : PuncturedAcyclic N twoR z)
    {rel : ModuleCat.{0} (ZMod 2)}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom) :
    Function.Surjective j.hom := by
  haveI := hacyclic.subsingleton_punctured_top
  exact ModuleCat.hom_surjective_of_exact_of_subsingleton j i hexact

/-- **Step C, assembled.**  A rank-`r` bundle over `N` carrying a section whose only zero
is `z` and which is a local homeomorphism there has nonzero top mod-2 Chern class.

The hypotheses, in the order in which the mathematics produces them:

* `hacyclic` — `N` is a product of spheres and complex projective spaces of total
  dimension `twoR`, so `H^{twoR}(N ∖ z; F₂) = 0` (`PuncturedAcyclic.prod`);
* `j`, `i`, `hexact` — the long exact sequence of the pair `(N, N ∖ z)` at `H^{twoR}(N)`
  (`cc-relative`, need (B2));
* `relEquiv`, `absEquiv` — both `H^{twoR}(N, N ∖ z; F₂)` and `H^{twoR}(N; F₂)` are one
  dimensional, the first by excision to a chart, the second by Künneth
  (`cc-relative` (B3)/(B6), `cc-cohom-api` (A7));
* `exc`, `hexc`, `hg` — the relative Euler class excises to the nonzero local generator
  (`cc-relative` (B3)/(B4)/(B6), `cc-bundle` (C3)/(C4));
* `hgamma` — `γ_r(W) = j^*(s^* u)` (`cc-projective` (D1) and the Thom-class construction
  of `ThomFreeModule.lean`). -/
theorem topChernClass_ne_zero (hacyclic : PuncturedAcyclic N twoR z)
    {rel loc : ModuleCat.{0} (ZMod 2)}
    (j : rel ⟶ cohomologyZMod2 (TopCat.of N) twoR)
    (i : cohomologyZMod2 (TopCat.of N) twoR
          ⟶ cohomologyZMod2 (TopCat.of ↥({z}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range j.hom = LinearMap.ker i.hom)
    (relEquiv : rel ≃ₗ[ZMod 2] ZMod 2)
    (absEquiv : cohomologyZMod2 (TopCat.of N) twoR ≃ₗ[ZMod 2] ZMod 2)
    (exc : rel ⟶ loc) {su : rel} {g : loc} (hexc : exc.hom su = g) (hg : g ≠ 0)
    {gamma : cohomologyZMod2 (TopCat.of N) twoR} (hgamma : gamma = j.hom su) :
    gamma ≠ 0 := by
  have hsu : su ≠ 0 := ne_zero_of_map_ne_zero exc (by rw [hexc]; exact hg)
  have hsurj := surjective_of_punctured_acyclic hacyclic j i hexact
  rw [hgamma]
  exact ModuleCat.ne_zero_of_surjective_of_linearEquiv relEquiv absEquiv hsurj hsu

end StepC

end GroupApproximation.CharClass
