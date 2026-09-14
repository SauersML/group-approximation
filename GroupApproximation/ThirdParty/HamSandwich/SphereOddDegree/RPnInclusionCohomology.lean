/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.InducedOnRPCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RealProjectiveSpaceInclusion

































noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The restriction pullback `ī^* : H^k(RPⁿ⁺¹; F₂) → H^k(RPⁿ; F₂)` of the
equatorial projective inclusion `rpInclusion n : RPⁿ ↪ RPⁿ⁺¹`. -/
noncomputable def rpInclusionCohPullback (n k : ℕ) :
    rpCohomology (n + 1) k ⟶ rpCohomology n k :=
  (singularCohomologyZMod2 k).map (TopCat.ofHom (rpInclusion n)).op

/-- The restriction pullback `i^* : H^k(Sⁿ⁺¹; F₂) → H^k(Sⁿ; F₂)` of the equatorial
sphere inclusion `sphereInclusion n : Sⁿ ↪ Sⁿ⁺¹`. -/
noncomputable def sphereInclusionCohPullback (n k : ℕ) :
    sphereCohomology (n + 1) k ⟶ sphereCohomology n k :=
  (singularCohomologyZMod2 k).map (TopCat.ofHom (sphereInclusion n)).op

/-- The projective restriction pullback is the project's generic cohomology
pullback of `rpInclusion n`. -/
theorem rpInclusionCohPullback_eq_cohPullback (n k : ℕ) :
    rpInclusionCohPullback n k = cohPullback (TopCat.ofHom (rpInclusion n)) k :=
  rfl

/-- The sphere restriction pullback is the project's generic cohomology pullback
of `sphereInclusion n`. -/
theorem sphereInclusionCohPullback_eq_cohPullback (n k : ℕ) :
    sphereInclusionCohPullback n k
      = cohPullback (TopCat.ofHom (sphereInclusion n)) k :=
  rfl

/-- **Double-cover naturality square for the equatorial inclusion.** The
restriction pullbacks fit into the commuting square

```text
ī^* ≫ proj^* = proj^* ≫ i^*    : H^k(RPⁿ⁺¹; F₂) ⟶ H^k(Sⁿ; F₂).
```

This is the cohomological image of the point-set commuting square
`rpInclusion_comp_proj` (`ī ∘ proj = proj ∘ i`). It relates the restriction map
on `RP` cohomology to the restriction map on sphere cohomology through the double
cover, and is the input the cellular/LES computation reads on the top class. -/
theorem rpInclusion_pullback_naturality (n k : ℕ) :
    rpInclusionCohPullback n k ≫ projPullback n k
      = projPullback (n + 1) k ≫ sphereInclusionCohPullback n k := by
  rw [rpInclusionCohPullback, projPullback, projPullback, sphereInclusionCohPullback,
    ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← TopCat.ofHom_comp,
    ← TopCat.ofHom_comp, rpInclusion_comp_proj]

























/-- The cochain-level restriction map `C^•(RPⁿ⁺¹; F₂) ⟶ C^•(RPⁿ; F₂)` induced by
the equatorial inclusion. Its homology in degree `k` is `rpInclusionCohPullback`. -/
noncomputable def rpInclusionCochainMap (n : ℕ) :
    singularCochainComplexZMod2.obj (Opposite.op (TopCat.of (RP (n + 1)))) ⟶
      singularCochainComplexZMod2.obj (Opposite.op (TopCat.of (RP n))) :=
  singularCochainComplexZMod2.map (TopCat.ofHom (rpInclusion n)).op

/-- The restriction pullback on cohomology is the homology (in degree `k`) of the
cochain-level restriction map: `ī^* = H^k(rpInclusionCochainMap n)`. -/
theorem rpInclusionCohPullback_eq_homologyMap (n k : ℕ) :
    rpInclusionCohPullback n k
      = (HomologicalComplex.homologyFunctor _ _ k).map (rpInclusionCochainMap n) :=
  rfl

/-- The **relative cochain complex** `C^•(RPⁿ⁺¹, RPⁿ; F₂)` of the pair, defined as
the kernel of the cochain-level restriction map. -/
noncomputable def rpPairRelativeCochainComplex (n : ℕ) :
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  kernel (rpInclusionCochainMap n)

/-- The **relative cohomology** `H^k(RPⁿ⁺¹, RPⁿ; F₂)` of the pair, defined as the
`k`-th homology of the relative cochain complex. This is a genuine
`ModuleCat (ZMod 2)`-object. -/
noncomputable def rpPairRelativeCohomology (n k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (rpPairRelativeCochainComplex n).homology k

/-- The inclusion of the relative cochain complex into the absolute one,
`C^•(RPⁿ⁺¹, RPⁿ; F₂) ↪ C^•(RPⁿ⁺¹; F₂)` (the kernel inclusion). -/
noncomputable def rpPairRelativeι (n : ℕ) :
    rpPairRelativeCochainComplex n ⟶
      singularCochainComplexZMod2.obj (Opposite.op (TopCat.of (RP (n + 1)))) :=
  kernel.ι (rpInclusionCochainMap n)

/-- The relative inclusion followed by the restriction is zero (kernel
condition): this is the chain-level half-exactness `ι ≫ restr = 0`. -/
theorem rpPairRelative_comp_eq_zero (n : ℕ) :
    rpPairRelativeι n ≫ rpInclusionCochainMap n = 0 :=
  kernel.condition _

/-- The short complex of the pair
`C^•(RPⁿ⁺¹, RPⁿ; F₂) → C^•(RPⁿ⁺¹; F₂) → C^•(RPⁿ; F₂)`.
It is exact at the left two spots (a kernel short complex); it is a short exact
sequence iff `rpInclusionCochainMap n` is an epimorphism, in which case the long
exact cohomology sequence of the pair follows from
`HomologicalComplex.HomologySequence`. -/
noncomputable def rpPairShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :=
  ShortComplex.mk (rpPairRelativeι n) (rpInclusionCochainMap n)
    (rpPairRelative_comp_eq_zero n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
