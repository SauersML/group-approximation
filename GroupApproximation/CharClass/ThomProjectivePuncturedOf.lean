import GroupApproximation.CharClass.ThomProjectivePunctured
import GroupApproximation.CharClass.ThomKunnethOf
import GroupApproximation.Meta.AxiomGuard

/-!
# `ℂP^d` is top-punctured acyclic over a field

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomProjectivePunctured.lean` gives the projective base case of the punctured-product
recursion at `F₂`: `ℂP^d` is top-punctured acyclic at every point, and its punctured space is
a Künneth factor.  The mod-2 proof takes the vanishing of `H^k(ℂP^d)` above `2d` from the
full computation of `H^*(ℂP^d; F₂)`.  Only the vanishing is used, and over a field it follows
from `kunnethFactor_CPOf` with a point as the first factor, so no computation of the
cohomology ring of `ℂP^d` over `K` is needed here.

## Main declarations

* `isZero_cohomology_CPOf` — `H^k(ℂP^d; K) = 0` for `k > 2d`.
* `KunnethFactorOf.congrHomotopy` — being a Künneth factor transports along a homotopy
  equivalence.
* `puncturedAcyclic_CPOf` — **`ℂP^d` is top-punctured acyclic over a field at every point**.
* `kunnethFactor_CP_puncturedOf` — the punctured `ℂP^d` is a Künneth factor over a field.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

/-- **`H^k(ℂP^d; K) = 0` above `2d`**, from `ℂP^d` being a Künneth factor of dimension `2d`
with a point as the first factor. -/
theorem isZero_cohomology_CPOf (K : Type) [Field K] (d k : ℕ) (hk : 2 * d < k) :
    IsZero (Hmod K (TopCat.of (CP d)) k) := by
  have h := (kunnethFactor_CPOf K d).prod Unit 0
    (fun a ha => cohomology_unit_isZeroOf K a ha) k (by omega)
  exact thomIsZero_of_linearEquiv
    (pullEquivOfHomotopyEquivOf K (Homeomorph.uniqueProd Unit (CP d)).toHomotopyEquiv k) h

/-- **Being a Künneth factor transports along a homotopy equivalence**, over any commutative
ring. -/
theorem KunnethFactorOf.congrHomotopy {K : Type} [CommRing K] {Y W : Type} [TopologicalSpace Y]
    [TopologicalSpace W] {q : ℕ} (e : ContinuousMap.HomotopyEquiv Y W)
    (h : KunnethFactorOf K W q) : KunnethFactorOf K Y q :=
  ⟨fun A _ p hA k hk => thomIsZero_of_linearEquiv
    (pullEquivOfHomotopyEquivOf K ((ContinuousMap.HomotopyEquiv.refl A).prodCongr e) k).symm
    (h.prod A p hA k hk)⟩

/-- **`ℂP^d` is top-punctured acyclic at every point, over a field.**  Move the point to the
base point by a homeomorphism; the punctured space retracts onto `ℂP^{d-1}`, whose
cohomology vanishes above `2d - 2`. -/
theorem puncturedAcyclic_CPOf (K : Type) [Field K] :
    ∀ d : ℕ, 0 < d → ∀ w : CP d, PuncturedAcyclicOf K (CP d) (2 * d) w := by
  rintro (_ | d) hd w
  · omega
  · obtain ⟨e, he⟩ := exists_homeomorph_mapsTo_basePoint (d + 1) w
    refine PuncturedAcyclicOf.congr' (cohomologyToolkitOf K) e he ?_
    refine puncturedAcyclic_of_homotopyEquiv (cohomologyToolkitOf K) (by omega)
      (fun k hk => isZero_cohomology_CPOf K (d + 1) k hk) ?_
      (fun k hk => isZero_cohomology_CPOf K d k hk) (by omega)
    exact punctOpenHomotopyEquiv d

/-- **The complement of a point in `ℂP^d` is a Künneth factor over a field.** -/
theorem kunnethFactor_CP_puncturedOf (K : Type) [Field K] :
    ∀ d : ℕ, 0 < d → ∀ w : CP d, KunnethFactorOf K ↥({w}ᶜ : Set (CP d)) (2 * d - 1) := by
  rintro (_ | d) hd w
  · omega
  · obtain ⟨e, he⟩ := exists_homeomorph_mapsTo_basePoint (d + 1) w
    have hset : ({e w}ᶜ : Set (CP (d + 1))) = ({basePoint (d + 1)}ᶜ : Set (CP (d + 1))) := by
      rw [he]
    refine KunnethFactorOf.congrHomotopy
      (((homeomorphCompl e w).trans (Homeomorph.setCongr hset)).toHomotopyEquiv.trans
        (punctOpenHomotopyEquiv d)) ?_
    exact (kunnethFactor_CPOf K d).mono (by omega)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms isZero_cohomology_CPOf
#audit_axioms puncturedAcyclic_CPOf
#audit_axioms kunnethFactor_CP_puncturedOf

end

end GroupApproximation.CharClass
