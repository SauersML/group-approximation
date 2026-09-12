import GroupApproximation.CharClass.LIXStepDGenReal
import GroupApproximation.CharClass.ParityPSplitStepDNarrow
import GroupApproximation.Meta.AxiomGuard

/-!
# The Wu field of Step D mod `p` from the narrowed splitting principle

Lane `lx-bundleP` of the LIX strongest swarm (`notes/lix-strong-swarm/lx-bundleP.md`).

The field `wu` of `Gen.RealBundleModP` (`CharClass/LIXStepDGenReal.lean`) is the diagonal Wu
relation `P^i(γ_{i+1}) = c_i · γ_{ip+1} + (decomposables)` in the even part of the mapping torus.
`Gen.realWu_of_splitting` derives it from the strong splitting principle, whose `PowerData` asks
`P⁰ = id` on the whole flag algebra and intertwining at every class.  The reduced powers of the
torus supply neither, so this file derives the same field from lane `lx-splitK`'s **narrowed**
form (`ParityP.HasSplittingPN` over `ParityP.PowerDataN`): `P⁰` is the identity on `1` and on the
roots, the Cartan formula holds for a root times a product of roots, and the powers of the torus
intertwine only at the classes `γ (i + 1)`.  The computation is `ParityP.wu_field_of_splittingN`
with `ι := Gen.evenMap K pY` and the powers `T.PN` of the torus.

## Main results

* `Gen.realWu_of_splittingN` — the field `wu` from the components of a narrowed splitting.
* `Gen.realWu_of_hasSplittingPN` — the same from `ParityP.HasSplittingPN` directly, for a family
  of even classes.
* `Gen.isUnit_realWuLeading` — the leading coefficient `m^i · wuCoeff p i` is a unit.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open ParityP

namespace Gen

/-- **The field `wu` of `Gen.RealBundleModP` from a narrowed splitting**: an injective ring map `ρ`
of the even part of `N` into a ring carrying narrowed reduced-power data `D` whose elementary
symmetric functions are the images of the classes, intertwining the powers of the torus at the
classes `γ (i + 1)`, with normalisation the integer `m`.  The leading coefficient is
`m^i · wuCoeff p i`. -/
theorem realWu_of_splittingN {n : ℕ} {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
    {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
    {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}
    (T : RealTorusModP n K pY q₁ qodd σ₁ σodd) {p : ℕ} (hp : 2 ≤ p) {γ : ℕ → TotalHOf K N}
    (hγe : ∀ k, TotalHOf.IsEven (γ k)) {σ A : Type*} [CommRing A] [DecidableEq σ]
    (D : PowerDataN σ A p) (ρ : evenPart K N →+* A) (hρ : Function.Injective ρ)
    (hγ : ∀ k, ρ (⟨γ k, hγe k⟩ : evenPart K N) = D.gamma k)
    (hP : ∀ i : ℕ, ρ (T.PN i (⟨γ (i + 1), hγe (i + 1)⟩ : evenPart K N))
      = D.P i (ρ (⟨γ (i + 1), hγe (i + 1)⟩ : evenPart K N)))
    (m : ℤ) (hκ : D.κ = (m : A)) (i : ℕ) :
    IsDecomposable (fun k => (⟨γ k, hγe k⟩ : evenPart K N)) (i * p + 1)
      (T.PN i (⟨γ (i + 1), hγe (i + 1)⟩ : evenPart K N)
        - evenMap K pY ((m ^ i * wuCoeff p i : ℤ) : evenPart K Y)
          * (⟨γ (i * p + 1), hγe (i * p + 1)⟩ : evenPart K N)) :=
  wu_field_of_splittingN hp (evenMap K pY) D ρ hρ (fun k => (⟨γ k, hγe k⟩ : evenPart K N)) hγ
    T.PN hP m hκ i

/-- **The field `wu` from `ParityP.HasSplittingPN`**, for a family `Γ` of even classes and the
reduced powers `T.PN` of the torus. -/
theorem realWu_of_hasSplittingPN {n : ℕ} {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
    {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
    {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}
    (T : RealTorusModP n K pY q₁ qodd σ₁ σodd) {p : ℕ} (hp : 2 ≤ p) (Γ : ℕ → evenPart K N)
    (m : ℤ) (hwu : HasSplittingPN p Γ T.PN m) (i : ℕ) :
    IsDecomposable Γ (i * p + 1)
      (T.PN i (Γ (i + 1)) - evenMap K pY ((m ^ i * wuCoeff p i : ℤ) : evenPart K Y) * Γ (i * p + 1)) := by
  obtain ⟨A, _, σ, _, D, ρ, hρ, hγ, hP, hκ⟩ := hwu
  exact wu_field_of_splittingN hp (evenMap K pY) D ρ hρ Γ hγ T.PN hP m hκ i

/-- **The leading coefficient is a unit**, once `p = 0` on `Y` and the normalisation is a unit. -/
theorem isUnit_realWuLeading {K : Type} [CommRing K] {Y : TopCat.{0}} {p : ℕ}
    (hpY : (p : evenPart K Y) = 0) {m : ℤ} (hm : IsUnit (m : evenPart K Y)) (i : ℕ) :
    IsUnit ((m ^ i * wuCoeff p i : ℤ) : evenPart K Y) :=
  isUnit_wuLeading hpY hm i

end Gen

#audit_axioms Gen.realWu_of_splittingN
#audit_axioms Gen.realWu_of_hasSplittingPN
#audit_axioms Gen.isUnit_realWuLeading

end CharClass
end GroupApproximation

end
