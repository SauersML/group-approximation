import GroupApproximation.CharClass.LIXStepDGenReal
import GroupApproximation.CharClass.ChernSplittingOfPowers
import GroupApproximation.Meta.AxiomGuard

/-!
# The bundle data of Step D mod `p`, from its three geometric inputs

Lane `lx-bundleP` of the LIX strongest swarm (`notes/lix-strong-swarm/lx-bundleP.md`).

`CharClass/LIXStepDGenReal.lean` takes the bundle side of Step D mod `p` as the structure
`Gen.RealBundleModP`: evenness of the Chern classes, their two Künneth components with the degree
of the `z`-component, the slice class, and the diagonal Wu relation with a unit leading
coefficient.  This file builds that structure from three inputs of different kinds.  Each input
is stated as what its producer proves, and none of them mentions `a`, `b` or `c`:

* **Künneth** (`Gen.EvenKunnethSplitOf`): every class of `N` of even degree `2k` is
  `π_Y^* α + z · π_Y^* β` with `β` of degree `2(k − (n+1))`, and `β = 0` below the weight `n + 1`
  of `z = t x`.  This is a statement about the torus only.
* **The slice**: a section `s` of `π_Y` killing `z`, along which the Chern classes pull back to the
  coefficients of `∏ⱼ (1 + hⱼ)^{dⱼ}`.
* **The splitting principle** (`ParityP.HasSplittingP`), with an integer normalisation `m` that is
  a unit and `p = 0` on `Y`.  It gives `wu`, and `c i = m^i · wuCoeff p i` with its unit property,
  through `Gen.realWu_of_splitting` and `ParityP.isUnit_wuLeading`.

The components `a`, `b` are chosen from the Künneth statement.  The slice field holds for the
chosen `a` because the section reads it off:
`s^* γ = s^* π_Y^* a + s^* z · s^* π_Y^* b = a`.

## Main results

* `Gen.EvenKunnethSplitOf` — the Künneth input.
* `Gen.bundlePA`, `Gen.bundlePB`, `Gen.bundlePB_low`, `Gen.bundlePGamma_eq` — the chosen components.
* `Gen.bundlePA_eq_map` — the chosen `Y`-component is the slice pullback.
* `Gen.realBundleModP_of_split` — **the producer of `Gen.RealBundleModP`**.
* `Gen.gamma_top_eq_zero_of_split` — Step D mod `p` at the top index, from the same inputs.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open ParityP

namespace Gen

/-! ## 1. The Künneth input -/

/-- **The Künneth input of the bundle data.**  Every class of `N` in even degree `2k` is a pullback
from `Y` plus `z = t x` times a pullback of degree `2(k − (n + 1))`, and the second summand vanishes
below the weight `n + 1` of `z`.  At the mapping torus `N = S¹ × S^{2n+1} × Y` over a field this is
Künneth with two sphere factors and no odd cohomology on `Y`. -/
def EvenKunnethSplitOf (n : ℕ) (K : Type) [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
    (pY : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : TotalPieceOf K S₁ 1) (σodd : TotalPieceOf K Sodd (2 * n + 1)) : Prop :=
  ∀ (k : ℕ) (x : TotalPieceOf K N (2 * k)),
    ∃ (α : TotalPieceOf K Y (2 * k)) (β : TotalPieceOf K Y (2 * (k - (n + 1)))),
      (k < n + 1 → β = 0) ∧
        TotalHOf.of K N (2 * k) x
          = TotalHOf.map K pY (TotalHOf.of K Y (2 * k) α)
            + zClass K q₁ qodd σ₁ σodd
              * TotalHOf.map K pY (TotalHOf.of K Y (2 * (k - (n + 1))) β)

/-! ## 2. The chosen components -/

section Components

variable {n : ℕ} {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
  {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
  {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}

/-- The `Y`-component of the `k`-th class, chosen from the Künneth input. -/
def bundlePA (hsplit : EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd) (Γ : ℕ → evenPart K N)
    (hhom : ∀ k : ℕ, ∃ x : TotalPieceOf K N (2 * k),
      (Γ k : TotalHOf K N) = TotalHOf.of K N (2 * k) x)
    (k : ℕ) : TotalPieceOf K Y (2 * k) :=
  (hsplit k (hhom k).choose).choose

/-- The `z Y`-component of the `k`-th class, of degree `2(k − (n + 1))`. -/
def bundlePB (hsplit : EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd) (Γ : ℕ → evenPart K N)
    (hhom : ∀ k : ℕ, ∃ x : TotalPieceOf K N (2 * k),
      (Γ k : TotalHOf K N) = TotalHOf.of K N (2 * k) x)
    (k : ℕ) : TotalPieceOf K Y (2 * (k - (n + 1))) :=
  (hsplit k (hhom k).choose).choose_spec.choose

/-- The `z Y`-component vanishes below the weight of `z`. -/
theorem bundlePB_low (hsplit : EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd) (Γ : ℕ → evenPart K N)
    (hhom : ∀ k : ℕ, ∃ x : TotalPieceOf K N (2 * k),
      (Γ k : TotalHOf K N) = TotalHOf.of K N (2 * k) x)
    (k : ℕ) (hk : k < n + 1) : bundlePB hsplit Γ hhom k = 0 :=
  (hsplit k (hhom k).choose).choose_spec.choose_spec.1 hk

/-- **The Künneth decomposition of the classes**, at the chosen components. -/
theorem bundlePGamma_eq (hsplit : EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd) (Γ : ℕ → evenPart K N)
    (hhom : ∀ k : ℕ, ∃ x : TotalPieceOf K N (2 * k),
      (Γ k : TotalHOf K N) = TotalHOf.of K N (2 * k) x)
    (k : ℕ) :
    (Γ k : TotalHOf K N)
      = TotalHOf.map K pY (TotalHOf.of K Y (2 * k) (bundlePA hsplit Γ hhom k))
        + zClass K q₁ qodd σ₁ σodd
          * TotalHOf.map K pY
              (TotalHOf.of K Y (2 * (k - (n + 1))) (bundlePB hsplit Γ hhom k)) :=
  (hhom k).choose_spec.trans (hsplit k (hhom k).choose).choose_spec.choose_spec.2

/-- **The chosen `Y`-component is the slice pullback**, for a section `s` of `π_Y` killing `z`:
`s^* γ = s^* π_Y^* a + s^* z · s^* π_Y^* b = a`. -/
theorem bundlePA_eq_map (hsplit : EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd) (Γ : ℕ → evenPart K N)
    (hhom : ∀ k : ℕ, ∃ x : TotalPieceOf K N (2 * k),
      (Γ k : TotalHOf K N) = TotalHOf.of K N (2 * k) x)
    (s : Y ⟶ N) (hs : ∀ c : TotalHOf K Y, TotalHOf.map K s (TotalHOf.map K pY c) = c)
    (hsz : TotalHOf.map K s (zClass K q₁ qodd σ₁ σodd) = 0) (k : ℕ) :
    TotalHOf.of K Y (2 * k) (bundlePA hsplit Γ hhom k) = TotalHOf.map K s (Γ k : TotalHOf K N) := by
  rw [bundlePGamma_eq hsplit Γ hhom k, map_add, map_mul, hsz, zero_mul, add_zero, hs]

end Components

/-! ## 3. The producer -/

section Producer

variable {n p ℓ : ℕ} {dd : Fin ℓ → ℕ} {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
  {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
  {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}

/-- **The producer of `Gen.RealBundleModP`.**  From the torus data `T`, a homogeneous family `Γ`
of even classes (the Chern classes, `Γ k` in degree `2k`), the Künneth input, a section `s` of
`π_Y` killing `z` along which `Γ` pulls back to the slice class, and the splitting principle with a
unit normalisation `m` and `p = 0` on `Y`. -/
def realBundleModP_of_split (hp : 2 ≤ p) (T : RealTorusModP n K pY q₁ qodd σ₁ σodd)
    (Γ : ℕ → evenPart K N)
    (hhom : ∀ k : ℕ, ∃ x : TotalPieceOf K N (2 * k),
      (Γ k : TotalHOf K N) = TotalHOf.of K N (2 * k) x)
    (hsplit : EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd)
    (s : Y ⟶ N) (hs : ∀ c : TotalHOf K Y, TotalHOf.map K s (TotalHOf.map K pY c) = c)
    (hsz : TotalHOf.map K s (zClass K q₁ qodd σ₁ σodd) = 0)
    (gen : Fin ℓ → evenPart K Y)
    (hslice : ∀ q : ℕ, evenMap K s (Γ q) = (sliceClass Finset.univ gen dd).coeff q)
    (m : ℤ) (hpY : (p : evenPart K Y) = 0) (hm : IsUnit (m : evenPart K Y))
    (hwu : HasSplittingP p Γ (fun i => evenRestrictAdd (T.PN i) (T.PN_even i)) m) :
    RealBundleModP p dd T (fun k => (Γ k : TotalHOf K N)) where
  γ_even k := mem_evenPart.mp (Γ k).2
  a k := TotalHOf.of K Y (2 * k) (bundlePA hsplit Γ hhom k)
  b k := TotalHOf.of K Y (2 * (k - (n + 1))) (bundlePB hsplit Γ hhom k)
  a_even k := TotalHOf.isEven_of K Y (even_two_mul k) _
  b_even k := TotalHOf.isEven_of K Y (even_two_mul (k - (n + 1))) _
  γ_eq k := bundlePGamma_eq hsplit Γ hhom k
  b_low k hk :=
    (congrArg (TotalHOf.of K Y (2 * (k - (n + 1)))) (bundlePB_low hsplit Γ hhom k hk)).trans
      (map_zero _)
  b_deg k _ := ⟨bundlePB hsplit Γ hhom k, rfl⟩
  gen := gen
  slice q := by
    have h : (⟨TotalHOf.of K Y (2 * q) (bundlePA hsplit Γ hhom q),
        TotalHOf.isEven_of K Y (even_two_mul q) _⟩ : evenPart K Y) = evenMap K s (Γ q) :=
      Subtype.ext (bundlePA_eq_map hsplit Γ hhom s hs hsz q)
    exact h.trans (hslice q)
  c i := ((m ^ i * wuCoeff p i : ℤ) : evenPart K Y)
  c_isUnit i := isUnit_wuLeading hpY hm i
  wu i := by
    obtain ⟨A, _, σ, _, D, ρ, hρ, hγ, hP, hκ⟩ := hwu
    exact realWu_of_splitting T hp (fun k => mem_evenPart.mp (Γ k).2) D ρ hρ hγ hP m hκ i

/-- **Step D mod `p` at the top index, from the three inputs.**  If `p ∣ n` and `p` divides every
`dⱼ`, the class at the rank `(∑ⱼ dⱼ) + (n + 1)` vanishes. -/
theorem gamma_top_eq_zero_of_split (hp : 2 ≤ p) (hn : 1 ≤ n) (hpn : p ∣ n)
    (hd : ∀ j, p ∣ dd j) (T : RealTorusModP n K pY q₁ qodd σ₁ σodd)
    (Γ : ℕ → evenPart K N)
    (hhom : ∀ k : ℕ, ∃ x : TotalPieceOf K N (2 * k),
      (Γ k : TotalHOf K N) = TotalHOf.of K N (2 * k) x)
    (hsplit : EvenKunnethSplitOf n K pY q₁ qodd σ₁ σodd)
    (s : Y ⟶ N) (hs : ∀ c : TotalHOf K Y, TotalHOf.map K s (TotalHOf.map K pY c) = c)
    (hsz : TotalHOf.map K s (zClass K q₁ qodd σ₁ σodd) = 0)
    (gen : Fin ℓ → evenPart K Y)
    (hslice : ∀ q : ℕ, evenMap K s (Γ q) = (sliceClass Finset.univ gen dd).coeff q)
    (m : ℤ) (hpY : (p : evenPart K Y) = 0) (hm : IsUnit (m : evenPart K Y))
    (hwu : HasSplittingP p Γ (fun i => evenRestrictAdd (T.PN i) (T.PN_even i)) m)
    [ExpChar (evenPart K Y) p] :
    (Γ ((∑ j, dd j) + (n + 1)) : TotalHOf K N) = 0 :=
  (realBundleModP_of_split hp T Γ hhom hsplit s hs hsz gen hslice m hpY hm hwu).gamma_top_eq_zero
    hp hn hpn hd

end Producer

end Gen

#audit_axioms Gen.EvenKunnethSplitOf
#audit_axioms Gen.bundlePA
#audit_axioms Gen.bundlePB
#audit_axioms Gen.bundlePB_low
#audit_axioms Gen.bundlePGamma_eq
#audit_axioms Gen.bundlePA_eq_map
#audit_axioms Gen.realBundleModP_of_split
#audit_axioms Gen.gamma_top_eq_zero_of_split

end CharClass
end GroupApproximation

end
