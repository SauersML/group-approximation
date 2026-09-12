import GroupApproximation.CharClass.LIXStepDGenRealEven
import GroupApproximation.CharClass.LIXLemmaTwoGenGlue
import GroupApproximation.CharClass.ParityPWuTransport

/-!
# Step D mod `p` at the real mapping torus, over a coefficient ring `K`

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4; lead's ruling of 2026-09-11).

`CharClass/LIXStepDGenModP.lean` proves Step D mod `p` at rank `n` from `Gen.ModPStepDData`,
a structure over an abstract pair of commutative rings.  This file assembles that structure
at the **real** objects: the mapping torus `N` with its projections `pY : N → Y`,
`q₁ : N → S¹`, `qodd : N → S^{2n+1}`, the coefficient-generic cohomology rings
`TotalHOf K N`, `TotalHOf K Y` (`CharClass/ChernTotalRingOf.lean`), and their even parts
(`CharClass/LIXStepDGenRealEven.lean`), which are the commutative rings `R` and `H`.

The inputs are split by where they come from.

* `Gen.RealTorusModP` — what depends on the torus and not on the bundle: the vanishing of
  `H²(S¹; K)`, Künneth uniqueness for `z = t x`, and the reduced powers `P^i` on `N` and `Y`
  with `P⁰ = id`, the Cartan formula, naturality along `pY`, `P^{>0}` killing the two sphere
  classes, and instability on `Y`.  Owners: Künneth over `K` (`lix-lh`, `lix-coeff`), the
  operations (`lix-steenrod`).
* `Gen.RealBundleModP` — what depends on the bundle: evenness of its Chern classes, their two
  Künneth components, the degree of the `z`-component, the slice class, and the diagonal Wu
  relation with a unit leading coefficient.  Owners: Leray–Hirsch over `K` (`lix-lh`), the Wu
  relation (`lix-evenside`, through `Gen.realWu_of_splitting` below).

What this file proves, rather than assumes, is every field of `Gen.ModPStepDData` that is a
consequence of those inputs:

* `z² = 0` with **no sign**: `z = t x` is even, so it commutes with `t`, and
  `z z = (z t) x = (t z) x = (t t) x x = 0` from `H²(S¹) = 0` alone (`Gen.zClass_mul_self`);
* `P^{>0} z = 0` from the Cartan formula and `P^{>0} t = P^{>0} x = 0` (`RealTorusModP.PN_zClass`);
* instability at the single index the even side uses, from the degree of `b k` and
  instability on `Y` (`RealBundleModP.instability_b`);
* the restriction of everything to the even parts (`RealBundleModP.toModPStepDData`).

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
`z = t x`, and the reduced powers on `N` and `Y` in the form the even side uses. -/
structure RealTorusModP (n : ℕ) (K : Type) [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
    (pY : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : TotalPieceOf K S₁ 1) (σodd : TotalPieceOf K Sodd (2 * n + 1)) where
  /-- `H²(S¹; K) = 0`. -/
  circle_two : ∀ a : TotalPieceOf K S₁ (1 + 1), a = 0
  /-- Künneth uniqueness: the `z`-component of a class of `N` is well defined. -/
  z_inj : ∀ u v : TotalHOf K Y,
    TotalHOf.map K pY u + zClass K q₁ qodd σ₁ σodd * TotalHOf.map K pY v = 0 → v = 0
  /-- The reduced powers on `N`. -/
  PN : ℕ → TotalHOf K N →+ TotalHOf K N
  /-- The reduced powers on `Y`. -/
  PY : ℕ → TotalHOf K Y →+ TotalHOf K Y
  /-- `P^i` preserves evenness on `N` (it raises the degree by `2i(p − 1)`). -/
  PN_even : ∀ (i : ℕ) (x : TotalHOf K N), TotalHOf.IsEven x → TotalHOf.IsEven (PN i x)
  /-- `P^i` preserves evenness on `Y`. -/
  PY_even : ∀ (i : ℕ) (x : TotalHOf K Y), TotalHOf.IsEven x → TotalHOf.IsEven (PY i x)
  /-- `P⁰ = id`. -/
  PN_zero : ∀ x : TotalHOf K N, PN 0 x = x
  /-- The Cartan formula on `N`. -/
  cartan : ∀ (i : ℕ) (u v : TotalHOf K N),
    PN i (u * v) = ∑ j ∈ Finset.range (i + 1), PN j u * PN (i - j) v
  /-- Naturality along `pY`. -/
  natural : ∀ (i : ℕ) (r : TotalHOf K Y),
    PN i (TotalHOf.map K pY r) = TotalHOf.map K pY (PY i r)
  /-- The positive powers kill `t` (it lives on the circle). -/
  P_t : ∀ i : ℕ, 0 < i → PN i (tClassOf K q₁ σ₁) = 0
  /-- The positive powers kill `x` (it lives on the odd sphere). -/
  P_x : ∀ i : ℕ, 0 < i → PN i (xClassOf K qodd σodd) = 0
  /-- Instability on `Y`: `P^i` vanishes on classes of degree `< 2i`. -/
  PY_unstable : ∀ (i d : ℕ) (c : TotalPieceOf K Y d), d < 2 * i →
    PY i (TotalHOf.of K Y d c) = 0

namespace RealTorusModP

variable {n : ℕ} {K : Type} [CommRing K] {N Y S₁ Sodd : TopCat.{0}}
  {pY : N ⟶ Y} {q₁ : N ⟶ S₁} {qodd : N ⟶ Sodd}
  {σ₁ : TotalPieceOf K S₁ 1} {σodd : TotalPieceOf K Sodd (2 * n + 1)}
  (T : RealTorusModP n K pY q₁ qodd σ₁ σodd)

/-- **`P(z) = z`**: the positive powers kill `z = t x`, by Cartan. -/
theorem PN_zClass (i : ℕ) (hi : 0 < i) : T.PN i (zClass K q₁ qodd σ₁ σodd) = 0 := by
  rw [zClass, T.cartan]
  refine Finset.sum_eq_zero fun j _ => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [Nat.sub_zero, T.P_x i hi, mul_zero]
  · rw [T.P_t j hj, zero_mul]

/-- The powers on the even part of `N`. -/
def evenPN (i : ℕ) : evenPart K N →+ evenPart K N := evenRestrictAdd (T.PN i) (T.PN_even i)

/-- The powers on the even part of `Y`. -/
def evenPY (i : ℕ) : evenPart K Y →+ evenPart K Y := evenRestrictAdd (T.PY i) (T.PY_even i)

end RealTorusModP

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
    (evenRestrictAdd (T.PN i) (T.PN_even i) (⟨γ (i + 1), γ_even (i + 1)⟩ : evenPart K N)
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
theorem instability_b (k i : ℕ) (h : k < i + (n + 1)) : T.PY i (B.b k) = 0 := by
  by_cases hk : k < n + 1
  · rw [B.b_low k hk, map_zero]
  · obtain ⟨c, hc⟩ := B.b_deg k (by omega)
    rw [hc]
    exact T.PY_unstable i _ c (by omega)

/-- **The instance**: the real mod-`p` data is a `Gen.ModPStepDData` over the even parts. -/
def toModPStepDData : ModPStepDData n p dd (evenPart K Y) (evenPart K N) B.evenγ where
  ι := evenMap K pY
  z := evenZClass K q₁ qodd σ₁ σodd
  z_mul_z := Subtype.ext (zClass_mul_self K q₁ qodd σ₁ σodd ⟨n, rfl⟩ T.circle_two)
  z_inj u v h := Subtype.ext (T.z_inj u v (congrArg Subtype.val h))
  PH := T.evenPN
  PR := T.evenPY
  pH_zero u := Subtype.ext (T.PN_zero u)
  cartan i u v := Subtype.ext ((T.cartan i u v).trans
    (map_sum (evenPart K N).subtype (fun j => T.evenPN j u * T.evenPN (i - j) v)
      (Finset.range (i + 1))).symm)
  pH_z i hi := Subtype.ext (T.PN_zClass i hi)
  pH_ι i r := Subtype.ext (T.natural i r)
  a := B.evenA
  b := B.evenB
  γ_eq k := Subtype.ext (B.γ_eq k)
  instability := by
    intro k i h
    exact Subtype.ext (B.instability_b k i h)
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
    (hP : ∀ (i : ℕ) (x : evenPart K N),
      ρ (evenRestrictAdd (T.PN i) (T.PN_even i) x) = D.P i (ρ x))
    (m : ℤ) (hκ : D.κ = (m : A)) (i : ℕ) :
    IsDecomposable (fun k => (⟨γ k, hγe k⟩ : evenPart K N)) (i * p + 1)
      (evenRestrictAdd (T.PN i) (T.PN_even i) (⟨γ (i + 1), hγe (i + 1)⟩ : evenPart K N)
        - evenMap K pY ((m ^ i * wuCoeff p i : ℤ) : evenPart K Y)
          * (⟨γ (i * p + 1), hγe (i * p + 1)⟩ : evenPart K N)) :=
  wu_field_of_splitting hp (evenMap K pY) D ρ hρ (fun k => ⟨γ k, hγe k⟩) hγ
    (fun i => evenRestrictAdd (T.PN i) (T.PN_even i)) hP m hκ i

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
#audit_axioms Gen.RealTorusModP.PN_zClass
#audit_axioms Gen.RealBundleModP.instability_b
#audit_axioms Gen.RealBundleModP.toModPStepDData
#audit_axioms Gen.RealBundleModP.gamma_top_eq_zero
#audit_axioms Gen.realWu_of_splitting
#audit_axioms Gen.stepDHalf_of_realModP
#audit_axioms Gen.lemmaTwoFor_powers_of_stepC_realModP

end CharClass
end GroupApproximation

end
