import GroupApproximation.CharClass.RelHomotopyInvariance
import GroupApproximation.Meta.AxiomGuard

/-!
# A self-map of a pair joined to the identity acts trivially, over any ring

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

`CharClass/RelativeLineHomotopy.lean`'s `relPullback_eq_id_of_line` proves that an injective
self-map of a pair induces the identity on a relative group that is an `F₂`-**line**, from the
fact that an `F₂`-line has one nonzero element.  Over a field with more than two elements that
argument is gone: an injective endomorphism of a `K`-line is multiplication by a unit, and a
unit need not be `1`.  What survives at every coefficient ring is the homotopy version: a
self-map joined to the identity by a homotopy through maps of pairs induces the identity, in
every degree and with no hypothesis on the relative group.  This file states it in the two
shapes the consumers use, as corollaries of `RelHomotopyInvariance`.

For `LIXHsqLinear.relPullback_lixKHomeo_eq_id` the homotopy is the linear one,
`H (t, v) = γ t *ᵥ v` for a path `γ` in `GL_r(ℂ)` from the far-end matrix to `1`: every `γ t`
is invertible, so `H` carries `I × (ℂ^r ∖ 0)` into `ℂ^r ∖ 0`, which is `hH` verbatim.  That
geometry belongs to the file's owner; this file supplies the cohomological half.

## Main results

* `RelativeSupport.relPullback_eq_id_of_homotopy` — the homotopy form.
* `RelativeSupport.relPullback_eq_id_of_contractible_param` — the parameter-space form, the
  interface of `RelativeLineHomotopy.relPullback_eq_of_homotopy_of_line` with the far slice
  the identity.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

namespace RelativeSupport

noncomputable section

/-- **A self-map of a pair joined to the identity by a homotopy of pairs induces the identity
on relative cohomology**, over any commutative ring and in every degree. -/
theorem relPullback_eq_id_of_homotopy (R : Type) [CommRing R] {X : TopCat.{0}} {A : Set X}
    {f : X ⟶ X} (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A)
    (H : TopCat.Homotopy f (𝟙 X))
    (hH : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ A) (n : ℕ) :
    relPullback R f hf n = 𝟙 (relCohomology R X A n) :=
  (relPullback_eq_of_homotopy R hf (fun _ hx => hx) H hH n).trans
    (relPullback_id R X A (fun _ hx => hx) n)

/-- **The parameter-space form.**  A map out of `P × E` preserving `P × A`, with `P`
contractible, whose slice at `b` is `f` and whose slice at `b'` is the identity: then `f`
induces the identity on `H^n(E, A; R)`. -/
theorem relPullback_eq_id_of_contractible_param (R : Type) [CommRing R]
    {P : Type} [TopologicalSpace P] {E : Type} [TopologicalSpace E] {A : Set E}
    (hP : ContractibleSpace P) (b b' : P) (Hm : TopCat.of (P × E) ⟶ TopCat.of E)
    (hHm : ∀ q ∈ {q : P × E | q.2 ∈ A}, (ConcreteCategory.hom Hm) q ∈ A)
    {f : TopCat.of E ⟶ TopCat.of E}
    (hbf : sliceMap b E ≫ Hm = f) (hbg : sliceMap b' E ≫ Hm = 𝟙 (TopCat.of E))
    (hf : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A) (n : ℕ) :
    relPullback R f hf n = 𝟙 (relCohomology R (TopCat.of E) A n) :=
  (relPullback_eq_of_contractible_param R hP b b' Hm hHm hbf hbg hf (fun _ hx => hx) n).trans
    (relPullback_id R (TopCat.of E) A (fun _ hx => hx) n)

end

end RelativeSupport

/-! Audited on every build. -/

#audit_axioms RelativeSupport.relPullback_eq_id_of_homotopy
#audit_axioms RelativeSupport.relPullback_eq_id_of_contractible_param

end GroupApproximation.CharClass
