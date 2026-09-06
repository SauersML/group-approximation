import GroupApproximation.CharClass.BundleTotalOver
import GroupApproximation.CharClass.RelativeFunctorial
import GroupApproximation.CharClass.CohomologyBridge

/-!
# Restricting a bundle pair twice, without comparing to a direct restriction

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

The fibre route for `hres` restricts the bundle pair to a trivialising
neighbourhood and then again to a point of it, so that the far end has a
**compact** base where `cc-projective`'s `lerayHirschGraded_compact` applies with
nothing added.

It was thought this needed transitivity of `Bundle.restrictTo`, and so a decision
about whether to compare a restriction of a restriction with a direct
restriction: the first lives over a subtype of a subtype, the second over a
subtype of the base.  It does not.  Composing `cc-bundle`'s two inclusions and
pulling back once is enough, and the direct restriction never appears, so the two
subtypes are never identified and no shape has to be chosen.

That is the whole content of this file: `totalInclOn` is generic in the base, so
it applies again at the restricted bundle, and `relPullback_comp` turns the
composite into the factorisation.

**What this does not do.**  It does not say the composite agrees with restricting
directly to a point of the ambient base; that statement is still unproved and
still needs the identification this file avoids.  Nothing downstream should read
the factorisation below as that.

## Main declarations

* `Bundle.totalInclOnComp` — the two inclusions composed.
* `Bundle.totalInclOnComp_mem_puncturedSet_iff` — it is a map of punctured pairs.
* `relPullback_totalInclOn_comp` — **the factorisation on relative cohomology.**
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace Bundle

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The inclusion of a twice-restricted total space, as one map. -/
def totalInclOnComp (p : Bundle X ι) (U : Set X) (V : Set ↥U) :
    C(Total ((p.restrictTo U).restrictTo V), Total p) :=
  (totalInclOn p U).comp (totalInclOn (p.restrictTo U) V)

@[simp] theorem totalInclOnComp_apply (p : Bundle X ι) (U : Set X) (V : Set ↥U)
    (w : Total ((p.restrictTo U).restrictTo V)) :
    totalInclOnComp p U V w = totalInclOn p U (totalInclOn (p.restrictTo U) V w) :=
  rfl

/-- **The composite is a map of punctured pairs**, in both directions, by two
applications of `cc-bundle`'s membership equivalence. -/
theorem totalInclOnComp_mem_puncturedSet_iff (p : Bundle X ι) (U : Set X)
    (V : Set ↥U) (w : Total ((p.restrictTo U).restrictTo V)) :
    ((totalInclOnComp p U V w : Total p) : X × (ι → ℂ)) ∈ puncturedSet p
      ↔ (w : ↥V × (ι → ℂ)) ∈ puncturedSet ((p.restrictTo U).restrictTo V) :=
  (totalInclOn_mem_puncturedSet_iff p U (totalInclOn (p.restrictTo U) V w)).trans
    (totalInclOn_mem_puncturedSet_iff (p.restrictTo U) V w)

end Bundle

/-! ## The factorisation on relative cohomology -/

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- **Restricting twice is restricting, then restricting.**  The direct
restriction to a point of the ambient base never appears, so the subtype of a
subtype is never identified with a subtype of the base. -/
theorem relPullback_totalInclOn_comp (p : Bundle X ι) (U : Set X) (V : Set ↥U)
    (n : ℕ)
    (hU : ∀ w ∈ {w : Bundle.Total (p.restrictTo U) |
        (w : ↥U × (ι → ℂ)) ∈ Bundle.puncturedSet (p.restrictTo U)},
      (ConcreteCategory.hom (cmap (Bundle.totalInclOn p U))) w
        ∈ {v : Bundle.Total p | (v : X × (ι → ℂ)) ∈ Bundle.puncturedSet p})
    (hV : ∀ w ∈ {w : Bundle.Total ((p.restrictTo U).restrictTo V) |
        (w : ↥V × (ι → ℂ)) ∈ Bundle.puncturedSet ((p.restrictTo U).restrictTo V)},
      (ConcreteCategory.hom (cmap (Bundle.totalInclOn (p.restrictTo U) V))) w
        ∈ {w : Bundle.Total (p.restrictTo U) |
          (w : ↥U × (ι → ℂ)) ∈ Bundle.puncturedSet (p.restrictTo U)})
    (hVU : ∀ w ∈ {w : Bundle.Total ((p.restrictTo U).restrictTo V) |
        (w : ↥V × (ι → ℂ)) ∈ Bundle.puncturedSet ((p.restrictTo U).restrictTo V)},
      (ConcreteCategory.hom
        (cmap (Bundle.totalInclOn (p.restrictTo U) V) ≫ cmap (Bundle.totalInclOn p U))) w
        ∈ {v : Bundle.Total p | (v : X × (ι → ℂ)) ∈ Bundle.puncturedSet p}) :
    relPullback (ZMod 2)
        (cmap (Bundle.totalInclOn (p.restrictTo U) V) ≫ cmap (Bundle.totalInclOn p U))
        hVU n
      = relPullback (ZMod 2) (cmap (Bundle.totalInclOn p U)) hU n
        ≫ relPullback (ZMod 2) (cmap (Bundle.totalInclOn (p.restrictTo U) V)) hV n :=
  relPullback_comp (ZMod 2) _ _ hV hU hVU n

/-! Printed on every build. -/

#print axioms relPullback_totalInclOn_comp

end

end GroupApproximation.CharClass
