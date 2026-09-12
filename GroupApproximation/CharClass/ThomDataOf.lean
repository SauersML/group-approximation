import GroupApproximation.CharClass.RelativeLES
import GroupApproximation.CharClass.ThomFreeDegreewise
import GroupApproximation.Meta.AxiomGuard

/-!
# The degreewise Thom data from the pair sequence, over any commutative ring

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`LIXThomAssembly.thomData_of_absToSub` builds the `ThomDeg` data of the pair at `F₂`, with
the coordinate reading of the top absolute group given by the mod-2 Leray–Hirsch equivalence
`lhTopEquiv`.  The argument uses nothing about that equivalence except that it is one: the
map out of the relative group is `relToAbs` followed by the inverse coordinate reading, its
injectivity is that of `relToAbs`, and its range is the hypothesis `habs`.

So over any commutative ring `K` the coordinate equivalence is taken as data `E`.  A consumer
over `F_p` instantiates it with the Leray–Hirsch equivalence over `K` once that exists, and
nothing here waits on it.  This file imports only the pair sequence and the Thom algebra, so
it stays out of the `F₂` `LIX*` closure.

## Main declarations

* `thomJmOf` — the map out of the relative group, in coordinates `E`.
* `thomData_of_absToSubOf` — **the `ThomDeg` data over `K`**, from `relToAbs` injective and
  `habs`.
-/

set_option autoImplicit false

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

/-- The map out of the relative group in coordinates: restrict to the absolute group, then
read coordinates through `E`. -/
def thomJmOf (K : Type) [CommRing K] {P : TopCat.{0}} {r : ℕ} {C : Type} [AddCommGroup C]
    [Module K C] (E : C ≃ₗ[K] Hmod K P (2 * r)) (Z : Set P) :
    ↥(relCohomology K P Z (2 * r)) →ₗ[K] C :=
  E.symm.toLinearMap.comp (relToAbs K P Z (2 * r)).hom

@[simp] theorem thomJmOf_apply (K : Type) [CommRing K] {P : TopCat.{0}} {r : ℕ} {C : Type}
    [AddCommGroup C] [Module K C] (E : C ≃ₗ[K] Hmod K P (2 * r)) (Z : Set P)
    (z : ↥(relCohomology K P Z (2 * r))) :
    thomJmOf K E Z z = E.symm ((relToAbs K P Z (2 * r)).hom z) := rfl

/-- **The degreewise Thom data over a commutative ring, from the pair sequence.**

`hinj0` is injectivity of `relToAbs`; `habs` identifies the range of the coordinate map
with the kernel of the coordinate map of the Chern relation.  Given those, `jm`, `hinj` and
`hrange` come out. -/
theorem thomData_of_absToSubOf (K : Type) [CommRing K] {P : TopCat.{0}} {r : ℕ} {C : Type}
    [AddCommGroup C] [Module K C] (E : C ≃ₗ[K] Hmod K P (2 * r)) (Z : Set P)
    {M : Fin (r + 1) → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (g : ∀ i : Fin r, M (Fin.last r) →ₗ[K] M i.castSucc)
    (coeff : C ≃ₗ[K] (∀ i, M i))
    (hinj0 : Function.Injective (relToAbs K P Z (2 * r)).hom)
    (habs : LinearMap.range (coeff.toLinearMap.comp (thomJmOf K E Z))
      = LinearMap.ker (ThomDeg.restrictMap g)) :
    ∃ (jm : ↥(relCohomology K P Z (2 * r)) →ₗ[K] (∀ i, M i))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap g) := by
  refine ⟨coeff.toLinearMap.comp (thomJmOf K E Z), ?_, habs⟩
  intro a b hab
  refine hinj0 ?_
  have h1 : E.symm ((relToAbs K P Z (2 * r)).hom a) = E.symm ((relToAbs K P Z (2 * r)).hom b) :=
    coeff.injective hab
  exact E.symm.injective h1

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms thomData_of_absToSubOf

end

end GroupApproximation.CharClass
