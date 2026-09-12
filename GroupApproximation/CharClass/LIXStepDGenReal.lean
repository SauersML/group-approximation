import GroupApproximation.CharClass.LIXStepDGenRealEven
import GroupApproximation.CharClass.LIXLemmaTwoGenGlue
import GroupApproximation.CharClass.ParityPWuTransport

/-!
# Step D mod `p` at the real mapping torus, over a coefficient ring `K`

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4; lead's ruling of 2026-09-11); restated on even
parts by lane `lx-torusP` (2026-09-12).

`CharClass/LIXStepDGenModP.lean` proves Step D mod `p` at rank `n` from `Gen.ModPStepDData`,
a structure over an abstract pair of commutative rings.  This file assembles that structure
at the **real** objects: the mapping torus `N` with its projections `pY : N → Y`,
`q₁ : N → S¹`, `qodd : N → S^{2n+1}`, the coefficient-generic cohomology rings
`TotalHOf K N`, `TotalHOf K Y` (`CharClass/ChernTotalRingOf.lean`), and their even parts
(`CharClass/LIXStepDGenRealEven.lean`), which are the commutative rings `R` and `H`.

The inputs are split by where they come from.

* `Gen.RealTorusModP` — what depends on the torus and not on the bundle: the vanishing of
  `H²(S¹; K)`, Künneth uniqueness for `z = t x`, and the reduced powers `P^i` on the **even
  parts** of `H^*(N)` and `H^*(Y)` with `P⁰ = id`, the Cartan formula, naturality along `pY`,
  `P^{>0} z = 0`, and instability on `Y`.  Every field about the operations is asked on even
  classes only, which is where the even side uses them: in odd degrees the construction's `P⁰`
  is a unit multiple of the identity and its Cartan formula carries signs, and nothing
  downstream needs either.  `P^{>0} z = 0` is asked for directly: `z` is pulled back from
  `S^{2n+1} × S¹`, whose cohomology vanishes above degree `2n + 2`, so it is a naturality
  statement (`CharClass/LIXStepDGenTorusPModel.lean`).  Owners: Künneth over `K`
  (`lx-kunneth`), the operations (`lx-pzero`), the torus producer (`lx-torusP`).
* `Gen.RealBundleModP` — what depends on the bundle: evenness of its Chern classes, their two
  Künneth components, the degree of the `z`-component, the slice class, and the diagonal Wu
  relation with a unit leading coefficient.  Owners: Leray–Hirsch over `K`, the Wu relation
  (`lx-splitK`, `lx-bundleP`, through `Gen.realWu_of_splitting` below).

What this file proves, rather than assumes, is every field of `Gen.ModPStepDData` that is a
consequence of those inputs:

* `z² = 0` with **no sign**: `z = t x` is even, so it commutes with `t`, and
  `z z = (z t) x = (t z) x = (t t) x x = 0` from `H²(S¹) = 0` alone (`Gen.zClass_mul_self`);
* instability at the single index the even side uses, from the degree of `b k` and
  instability on `Y` (`RealBundleModP.instability_b`);
* the restriction of the bundle data to the even parts (`RealBundleModP.toModPStepDData`).

## Main results

* `Gen.tClassOf`, `Gen.xClassOf`, `Gen.zClass`, `Gen.isEven_zClass`, `Gen.zClass_mul_self`,
  `Gen.evenZClass`.
* `Gen.RealTorusModP`, `Gen.RealBundleModP`, `Gen.RealBundleModP.toModPStepDData` — **the
  instance**.
* `Gen.RealBundleModP.gamma_top_eq_zero` — Step D mod `p` at the real mapping torus.
* `Gen.realWu_of_splitting` — the field `wu`, from `lix-evenside`'s split-family transport.
* `Gen.stepDHalf_of_realModP` — the Step D half of Lemma 2 at rank `n`, at the real objects.
* `Gen.lemmaTwoFor_powers_of_stepC_realModP` — Lemma 2 for the degree-`k` family at every
  stage, from the Step C half and the real mod-`p` data.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open ParityP

namespace Gen

/-! ## 1. The classes `t`, `x` and `z = t x` -/

section Classes

variable (K : Type) [CommRing K] {N S₁ Sodd : TopCat.{0}}

/-- The degree-one class `t`, pulled back from the circle factor. -/
def tClassOf (q₁ : N ⟶ S₁) (σ₁ : TotalPieceOf K S₁ 1) : TotalHOf K N :=
  TotalHOf.map K q₁ (TotalHOf.of K S₁ 1 σ₁)

/-- The class `x`, pulled back from the odd sphere factor, in any degree. -/
def xClassOf (qodd : N ⟶ Sodd) {c : ℕ} (σodd : TotalPieceOf K Sodd c) : TotalHOf K N :=
  TotalHOf.map K qodd (TotalHOf.of K Sodd c σodd)

/-- The class `z = t x`. -/
def zClass (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd) (σ₁ : TotalPieceOf K S₁ 1) {c : ℕ}
    (σodd : TotalPieceOf K Sodd c) : TotalHOf K N :=
  tClassOf K q₁ σ₁ * xClassOf K qodd σodd

/-- `z = t x` is even when `x` has odd degree: it is concentrated in degree `1 + c`. -/
theorem isEven_zClass (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd) (σ₁ : TotalPieceOf K S₁ 1) {c : ℕ}
    (σodd : TotalPieceOf K Sodd c) (hc : Odd c) :
    TotalHOf.IsEven (zClass K q₁ qodd σ₁ σodd) := by
  rw [zClass, tClassOf, xClassOf, TotalHOf.map_of, TotalHOf.map_of, ← TotalHOf.of_mul]
  refine TotalHOf.isEven_of K N ?_ _
  obtain ⟨r, hr⟩ := hc
  exact ⟨r + 1, by omega⟩

/-- `t² = 0` as soon as the circle has no cohomology in degree two. -/
theorem tClassOf_mul_self (q₁ : N ⟶ S₁) (σ₁ : TotalPieceOf K S₁ 1)
    (hS : ∀ a : TotalPieceOf K S₁ (1 + 1), a = 0) :
    tClassOf K q₁ σ₁ * tClassOf K q₁ σ₁ = 0 := by
  rw [tClassOf, ← map_mul (TotalHOf.map K q₁), ← TotalHOf.of_mul, hS (cup σ₁ σ₁), map_zero,
    map_zero]

/-- **`z² = 0`, with no sign.**  `z` is even, so it commutes with `t`, and
`z z = (z t) x = (t z) x = (t t) x x = 0`. -/
theorem zClass_mul_self (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd) (σ₁ : TotalPieceOf K S₁ 1) {c : ℕ}
    (σodd : TotalPieceOf K Sodd c) (hc : Odd c)
    (hS : ∀ a : TotalPieceOf K S₁ (1 + 1), a = 0) :
    zClass K q₁ qodd σ₁ σodd * zClass K q₁ qodd σ₁ σodd = 0 := by
  have hcomm : zClass K q₁ qodd σ₁ σodd * tClassOf K q₁ σ₁
      = tClassOf K q₁ σ₁ * zClass K q₁ qodd σ₁ σodd :=
    TotalHOf.mul_comm_of_isEven_left (isEven_zClass K q₁ qodd σ₁ σodd hc) _
  calc zClass K q₁ qodd σ₁ σodd * zClass K q₁ qodd σ₁ σodd
      = zClass K q₁ qodd σ₁ σodd * tClassOf K q₁ σ₁ * xClassOf K qodd σodd := by
        rw [mul_assoc, zClass]
    _ = tClassOf K q₁ σ₁ * tClassOf K q₁ σ₁ * xClassOf K qodd σodd * xClassOf K qodd σodd := by
        rw [hcomm, zClass, ← mul_assoc]
    _ = 0 := by rw [tClassOf_mul_self K q₁ σ₁ hS, zero_mul, zero_mul]

/-- `z = t x` at rank `n` (odd sphere of dimension `2n + 1`), as an element of the even part. -/
def evenZClass (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd) (σ₁ : TotalPieceOf K S₁ 1) {n : ℕ}
    (σodd : TotalPieceOf K Sodd (2 * n + 1)) : evenPart K N :=
  ⟨zClass K q₁ qodd σ₁ σodd, isEven_zClass K q₁ qodd σ₁ σodd ⟨n, rfl⟩⟩

end Classes

/-! ## 2. The torus data -/

/-- **The mod-`p` data of the mapping torus `N = S¹ × S^{2n+1} × Y`** that does not depend on
the bundle, over a coefficient ring `K`: the circle has no `H²`, Künneth uniqueness for
`z = t x`, and the reduced powers on the even parts of `H^*(N)` and `H^*(Y)` in the form the even
side uses. -/
structure RealTorusModP (n : ℕ) (K : Type) [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
    (pY : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : TotalPieceOf K S₁ 1) (σodd : TotalPieceOf K Sodd (2 * n + 1)) where
  /-- `H²(S¹; K) = 0`. -/
  circle_two : ∀ a : TotalPieceOf K S₁ (1 + 1), a = 0
  /-- Künneth uniqueness: the `z`-component of a class of `N` is well defined. -/
  z_inj : ∀ u v : TotalHOf K Y,
    TotalHOf.map K pY u + zClass K q₁ qodd σ₁ σodd * TotalHOf.map K pY v = 0 → v = 0
  /-- The reduced powers on the even part of `H^*(N)`. -/
  PN : ℕ → evenPart K N →+ evenPart K N
  /-- The reduced powers on the even part of `H^*(Y)`. -/
  PY : ℕ → evenPart K Y →+ evenPart K Y
  /-- `P⁰ = id`. -/
  PN_zero : ∀ x : evenPart K N, PN 0 x = x
  /-- The Cartan formula on the even part of `H^*(N)`. -/
  cartan : ∀ (i : ℕ) (u v : evenPart K N),
    PN i (u * v) = ∑ j ∈ Finset.range (i + 1), PN j u * PN (i - j) v
  /-- Naturality along `pY`. -/
  natural : ∀ (i : ℕ) (r : evenPart K Y), PN i (evenMap K pY r) = evenMap K pY (PY i r)
  /-- `P(z) = z`: the positive powers kill `z = t x`. -/
  P_z : ∀ i : ℕ, 0 < i → PN i (evenZClass K q₁ qodd σ₁ σodd) = 0
  /-- Instability on `Y`: `P^i` vanishes on classes of even degree `d < 2i`. -/
  PY_unstable : ∀ (i d : ℕ) (hd : Even d) (c : TotalPieceOf K Y d), d < 2 * i →
    PY i ⟨TotalHOf.of K Y d c, TotalHOf.isEven_of K Y hd c⟩ = 0

/-! ## 3. The bundle data, and the instance -/

/-- **The mod-`p` data of one bundle over the mapping torus**, with Chern classes `γ` in
`H^*(N; K)`: evenness, the Künneth components `a`, `b`, the degree of `b`, the slice class,
and the diagonal Wu relation with a unit leading coefficient, the last two read in the even
parts. -/
structure RealBundleModP {n : ℕ} (p : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ) {K : Type} [CommRing K]
    {N Y S₁ Sodd : TopCat.{0}} {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
    {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}
    (T : RealTorusModP n K pY q₁ qodd σ₁ σodd) (γ : ℕ → TotalHOf K N) where
  /-- The Chern classes are even. -/
  γ_even : ∀ k : ℕ, TotalHOf.IsEven (γ k)
  /-- The `H^*(Y)`-component of `γ k`. -/
  a : ℕ → TotalHOf K Y
  /-- The `z H^*(Y)`-component of `γ k`, indexed by the total index. -/
  b : ℕ → TotalHOf K Y
  /-- The components are even. -/
  a_even : ∀ k : ℕ, TotalHOf.IsEven (a k)
  /-- The components are even. -/
  b_even : ∀ k : ℕ, TotalHOf.IsEven (b k)
  /-- The Künneth decomposition of the Chern classes. -/
  γ_eq : ∀ k : ℕ,
    γ k = TotalHOf.map K pY (a k) + zClass K q₁ qodd σ₁ σodd * TotalHOf.map K pY (b k)
  /-- `b k = 0` below the weight of `z`. -/
  b_low : ∀ k : ℕ, k < n + 1 → b k = 0
  /-- `b k` has degree `2k − (2n + 2)`. -/
  b_deg : ∀ k : ℕ, n + 1 ≤ k →
    ∃ c : TotalPieceOf K Y (2 * (k - (n + 1))), b k = TotalHOf.of K Y _ c
  /-- The degree-two generators `hⱼ`. -/
  gen : Fin ℓ → evenPart K Y
  /-- The slice class of the bundle is `∏ⱼ (1 + hⱼ)^{dⱼ}`. -/
  slice : ∀ q : ℕ,
    (⟨a q, a_even q⟩ : evenPart K Y) = (sliceClass Finset.univ gen dd).coeff q
  /-- The leading coefficient of the diagonal Wu relation. -/
  c : ℕ → evenPart K Y
  /-- The leading coefficient is a unit. -/
  c_isUnit : ∀ i : ℕ, IsUnit (c i)
  /-- The diagonal Wu relation `P^i(γ_{i+1}) = c_i·γ_{ip+1} + (decomposables)`, in the even
  part of `N`. -/
  wu : ∀ i : ℕ, IsDecomposable (fun k => (⟨γ k, γ_even k⟩ : evenPart K N)) (i * p + 1)
    (T.PN i (⟨γ (i + 1), γ_even (i + 1)⟩ : evenPart K N)
      - evenMap K pY (c i) * (⟨γ (i * p + 1), γ_even (i * p + 1)⟩ : evenPart K N))

namespace RealBundleModP

variable {n p ℓ : ℕ} {dd : Fin ℓ → ℕ} {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
  {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
  {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}
  {T : RealTorusModP n K pY q₁ qodd σ₁ σodd} {γ : ℕ → TotalHOf K N}
  (B : RealBundleModP p dd T γ)

/-- The Chern classes, in the even part of `N`. -/
def evenγ : ℕ → evenPart K N := fun k => ⟨γ k, B.γ_even k⟩

/-- The `H^*(Y)`-components, in the even part of `Y`. -/
def evenA : ℕ → evenPart K Y := fun k => ⟨B.a k, B.a_even k⟩

/-- The `z H^*(Y)`-components, in the even part of `Y`. -/
def evenB : ℕ → evenPart K Y := fun k => ⟨B.b k, B.b_even k⟩

/-- **Instability at the index the even side uses**, from the degree of `b k` and instability
on `Y`: `P^i (b k) = 0` whenever `k < i + (n + 1)`. -/
theorem instability_b (k i : ℕ) (h : k < i + (n + 1)) : T.PY i (B.evenB k) = 0 := by
  by_cases hk : k < n + 1
  · have hb : B.evenB k = 0 := Subtype.ext (B.b_low k hk)
    rw [hb, map_zero]
  · obtain ⟨c, hc⟩ := B.b_deg k (by omega)
    have hb : B.evenB k
        = ⟨TotalHOf.of K Y _ c, TotalHOf.isEven_of K Y (even_two_mul (k - (n + 1))) c⟩ :=
      Subtype.ext hc
    rw [hb]
    exact T.PY_unstable i _ (even_two_mul (k - (n + 1))) c (by omega)

/-- **The instance**: the real mod-`p` data is a `Gen.ModPStepDData` over the even parts. -/
def toModPStepDData : ModPStepDData n p dd (evenPart K Y) (evenPart K N) B.evenγ where
  ι := evenMap K pY
  z := evenZClass K q₁ qodd σ₁ σodd
  z_mul_z := Subtype.ext (zClass_mul_self K q₁ qodd σ₁ σodd ⟨n, rfl⟩ T.circle_two)
  z_inj u v h := Subtype.ext (T.z_inj u v (congrArg Subtype.val h))
  PH := T.PN
  PR := T.PY
  pH_zero := T.PN_zero
  cartan := T.cartan
  pH_z := T.P_z
  pH_ι := T.natural
  a := B.evenA
  b := B.evenB
  γ_eq k := Subtype.ext (B.γ_eq k)
  instability k i h := B.instability_b k i h
  gen := B.gen
  slice := B.slice
  c := B.c
  c_isUnit := B.c_isUnit
  wu := B.wu

/-- **Step D mod `p` at the real mapping torus.**  If `p ∣ n` and `p` divides every `dⱼ`, the
Chern class of the bundle at the rank `(∑ⱼ dⱼ) + (n + 1)` vanishes in `H^*(N; K)`. -/
theorem gamma_top_eq_zero (B : RealBundleModP p dd T γ) (hp : 2 ≤ p) (hn : 1 ≤ n)
    [ExpChar (evenPart K Y) p] (hpn : p ∣ n) (hd : ∀ j, p ∣ dd j) :
    γ ((∑ j, dd j) + (n + 1)) = 0 :=
  congrArg Subtype.val (B.toModPStepDData.gamma_top_eq_zero hp hn hpn hd)

end RealBundleModP

/-! ## 4. The Wu field from a splitting -/

/-- **The field `wu` of `Gen.RealBundleModP`**, from `lix-evenside`'s transport of the
diagonal Wu relation along a splitting `ρ` of the even part of `N`, with leading coefficient
`m^i · wuCoeff p i`.  Its unit property is `ParityP.isUnit_wuLeading`. -/
theorem realWu_of_splitting {n : ℕ} {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
    {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
    {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}
    (T : RealTorusModP n K pY q₁ qodd σ₁ σodd) {p : ℕ} (hp : 2 ≤ p) {γ : ℕ → TotalHOf K N}
    (hγe : ∀ k, TotalHOf.IsEven (γ k)) {σ A : Type*} [CommRing A] [DecidableEq σ]
    (D : PowerData σ A p) (ρ : evenPart K N →+* A) (hρ : Function.Injective ρ)
    (hγ : ∀ k, ρ (⟨γ k, hγe k⟩ : evenPart K N) = D.gamma k)
    (hP : ∀ (i : ℕ) (x : evenPart K N), ρ (T.PN i x) = D.P i (ρ x))
    (m : ℤ) (hκ : D.κ = (m : A)) (i : ℕ) :
    IsDecomposable (fun k => (⟨γ k, hγe k⟩ : evenPart K N)) (i * p + 1)
      (T.PN i (⟨γ (i + 1), hγe (i + 1)⟩ : evenPart K N)
        - evenMap K pY ((m ^ i * wuCoeff p i : ℤ) : evenPart K Y)
          * (⟨γ (i * p + 1), hγe (i * p + 1)⟩ : evenPart K N)) :=
  wu_field_of_splitting hp (evenMap K pY) D ρ hρ (fun k => ⟨γ k, hγe k⟩) hγ T.PN hP m hκ i

/-! ## 5. The Step D half of Lemma 2 at the real objects -/

variable {ℓ : ℕ}

/-- **The Step D half of Lemma 2 at rank `n`, at the real mapping torus, mod `p`**: for a prime
`p ∣ n` dividing every `dⱼ`, the top Chern class vanishes on the mapping torus of every corner
unitary, given the torus data once and the bundle data for each corner unitary. -/
theorem stepDHalf_of_realModP (n p : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (hpn : p ∣ n)
    {dd : Fin ℓ → ℕ} (hd : ∀ j, p ∣ dd j) {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
    {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
    {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}
    (T : RealTorusModP n K pY q₁ qodd σ₁ σodd) [ExpChar (evenPart K Y) p]
    (γfun : (↥sphereOne × baseM n dd →
      Matrix (VIdx n dd ⊕ VIdx n dd) (VIdx n dd ⊕ VIdx n dd) ℂ) → ℕ → TotalHOf K N)
    (data : ∀ G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ, Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      RealBundleModP p dd T (γfun (mappingTorus (Vmat n) G circHoriz circHeight))) :
    StepDHalf n dd (fun W => γfun W ((∑ j, dd j) + (n + 1))) :=
  fun G hc hu => (data G hc hu).gamma_top_eq_zero hp.two_le hn hpn hd

/-- **Lemma 2 for the degree-`k` family at every stage, from the Step C half and the real
mod-`p` data.**  At a prime `p ∣ n`, given the torus data and the bundle data at every stage,
the Step C half at the top mod-`p` Chern class for every `k` with `p ∤ k` gives
`LIX.Gen.LemmaTwoFor n (lixDD n j) (KGen.bVecK n (k − 1))` at every stage `j`. -/
theorem lemmaTwoFor_powers_of_stepC_realModP (n p : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ n) {K : Type} [CommRing K] {N Y S₁ Sodd : ℕ → TopCat.{0}}
    {pY : ∀ j, N j ⟶ Y j} {q₁ : ∀ j, N j ⟶ S₁ j} {qodd : ∀ j, N j ⟶ Sodd j}
    {σ₁ : ∀ j, TotalPieceOf K (S₁ j) 1} {σodd : ∀ j, TotalPieceOf K (Sodd j) (2 * n + 1)}
    (T : ∀ j, RealTorusModP n K (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j))
    [∀ j, ExpChar (evenPart K (Y j)) p]
    (γfun : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → ℕ → TotalHOf K (N j))
    (data : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      RealBundleModP p (LIX.Gen.lixDD n j) (T j)
        (γfun j (mappingTorus (Vmat n) G circHoriz circHeight)))
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))
        (fun W => γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)))) :
    ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) :=
  lemmaTwoFor_powers_of_halves n p
    (fun j W => γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1))) hC
    (fun _ _ j => stepDHalf_of_realModP n p hp hn hpn (LIX.Gen.dvd_lixDD hpn j) (T j)
      (γfun j) (data j))

end Gen

#audit_axioms Gen.isEven_zClass
#audit_axioms Gen.tClassOf_mul_self
#audit_axioms Gen.zClass_mul_self
#audit_axioms Gen.evenZClass
#audit_axioms Gen.RealBundleModP.instability_b
#audit_axioms Gen.RealBundleModP.toModPStepDData
#audit_axioms Gen.RealBundleModP.gamma_top_eq_zero
#audit_axioms Gen.realWu_of_splitting
#audit_axioms Gen.stepDHalf_of_realModP
#audit_axioms Gen.lemmaTwoFor_powers_of_stepC_realModP

end CharClass
end GroupApproximation

end
