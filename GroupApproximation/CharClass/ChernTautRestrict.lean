import GroupApproximation.CharClass.ChernOfInvariance
import GroupApproximation.CharClass.BundleTautRestrict
import GroupApproximation.CharClass.BundleProjInclRange
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge

/-!
# The tautological class along the hyperplane inclusion

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`cc-thom`'s `thomData_total_of_lerayHirsch` takes the class on the hyperplane as a
parameter `ξ'` together with `hξ`, which says the tautological class of `P(E ⊕ 1)`
restricts to it.  This file supplies both.

The general fact is one lemma and it subsumes three uses.  A continuous map of
projectivisations that carries the tautological line to the tautological line *up
to isomorphism* carries the class to the class; the isomorphism is allowed to
change the index type, which is what makes it usable, since `tautEulerOf` reads
its `Fin` size off the index and the hyperplane changes that index from `ι` to
`ι ⊕ Unit`.  `CPn.eulerOfBundle_pushforward_iso` absorbs the size.

So `pull_tautEulerOf_of_iso` covers the base change (`projComap`), the bundle
isomorphism (`toTautIso`) and the hyperplane (`cc-bundle`'s `tautRestrictIso`)
with one statement, and the last of those is what `cc-thom` needs.

## Main declarations

* `pull_tautEulerOf_of_iso` — **the general fact.**
* `pull_projIncl_tautEulerOf` — the hyperplane, at `Proj p`.
* `tautEulerRange`, `pull_sInclusion_tautEulerOf` — **`ξ'` and `hξ`**, at the
  subspace presentation `cc-thom` works in.

## Manuscript status

Machinery.  Supplies the last topological input of the Thom bridge.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **A map that carries the tautological line to the tautological line carries the
class to the class.**

The isomorphism may change the index type, and in the two applications it does:
the hyperplane inclusion changes `ι` to `ι ⊕ Unit`.  That is why this cannot be
`eulerOfBundle_pushforward_congr`, which fixes the target `Fin`, and why it is
`CPn.eulerOfBundle_pushforward_iso`, which does not. -/
theorem pull_tautEulerOf_of_iso (a : Bundle X ι) (b : Bundle Y κ)
    (h : C(Proj b, Proj a))
    (e : BundleIso (comap h (tautLine a)) (tautLine b)) :
    pull (cmap h) 2 (tautEulerOf a) = tautEulerOf b := by
  have hcomap := eulerOfBundle_comap (show 1 ≤ 1 + tautCardOf ι by omega)
    (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine a))
    (CPn.trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine a)
      (trace_tautLine a))
    h
  refine hcomap.symm.trans ?_
  exact CPn.eulerOfBundle_pushforward_iso (1 + tautCardOf ι) (1 + tautCardOf κ)
    (by omega) (by omega) (comap h (tautLine a)) (tautLine b)
    (fun z => trace_tautLine a _) (trace_tautLine b) e
    (tautEmbOf_injective ι) (tautEmbOf_injective κ)

/-- **The hyperplane carries the class to the class**, at `Proj p`.  `cc-bundle`'s
`tautRestrictIso` is exactly the isomorphism the general fact asks for. -/
theorem pull_projIncl_tautEulerOf (p : Bundle X ι) :
    pull (cmap (projIncl p)) 2 (tautEulerOf p.plusOne) = tautEulerOf p :=
  pull_tautEulerOf_of_iso p.plusOne p (projIncl p) (tautRestrictIso p)

/-- **`ξ'`**: the tautological class of `P(p)`, carried to the hyperplane in its
subspace presentation. -/
def tautEulerRange [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    Hmod2 (TopCat.of ↥(Set.range (projIncl p))) 2 :=
  pull (cmap (⟨(projInclHomeoRange p).symm, (projInclHomeoRange p).symm.continuous⟩ :
    C(↥(Set.range (projIncl p)), Proj p))) 2 (tautEulerOf p)

/-- **`hξ`**, in the shape `thomData_total_of_lerayHirsch` takes it. -/
theorem pull_sInclusion_tautEulerOf [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    pull (sInclusion (Set.range (projIncl p))) 2 (tautEulerOf p.plusOne)
      = tautEulerRange p := by
  have hmap :
      (cmap (⟨(projInclHomeoRange p).symm, (projInclHomeoRange p).symm.continuous⟩ :
        C(↥(Set.range (projIncl p)), Proj p))) ≫ cmap (projIncl p)
        = sInclusion (X := TopCat.of (Proj p.plusOne)) (Set.range (projIncl p)) := by
    apply TopCat.Hom.ext
    refine ContinuousMap.ext fun w => ?_
    exact (projInclHomeoRange_coe p ((projInclHomeoRange p).symm w)).symm.trans
      (congrArg Subtype.val ((projInclHomeoRange p).apply_symm_apply w))
  simp only [tautEulerRange]
  rw [← pull_projIncl_tautEulerOf p, ← pull_comp, hmap]

end

end LH
end CharClass
end GroupApproximation
