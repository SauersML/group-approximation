import GroupApproximation.CharClass.SqDataInstance

/-!
# Step D at rank `n`: the even side over the generic objects

Lane `sp-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4).

`CharClass/ParityInstance.lean` and `CharClass/SqDataInstance.lean` put the even side of
Lemma 2 at the *rank-two* objects: the mapping torus is `N = S¹ × S⁵ × Y`, the Künneth
generator `x` has degree five, the `t x`-component `b k` has degree `2k − 6`, and the
conclusion is `γ_{m+3}(W) = 0`.  Three numbers there are the rank in disguise:

```text
5 = 2n + 1      the dimension of the odd sphere,
6 = 2n + 2      the degree of z = t x,
3 = n + 1       the rank of the trivial block 𝟏^{n+1}.
```

This file restates the whole even side with `n` as a parameter, and closes the loop by
re-deriving the landed rank-two endpoint from the generic one at `n = 2` (`§4`).

## The mathematics does not move

At `p = 2` the argument is uniform in the rank; §1.4 of the programme note and `sp-design`
§3 say why.  Concretely, nothing in `CharClass/ParityEven.lean` mentions the rank: its
`ParityData` is an abstract pair of rings with `t`, `x`, `γ`, `a`, `b`, and the rank enters
only through *which* index one reads the conclusion at.  So the generic even side is the
same structure with two changes:

* the instability field is asked for at the true degree of `b k` at rank `n`, namely
  `2 * k < j + (2 * n + 2)` rather than `2 * k < j + 6`.  For `2 ≤ n` this is the
  **stronger** hypothesis (`6 ≤ 2n + 2`), so it discharges the `ParityData` field and the
  landed convolution proof — `sum_a_mul_b_eq_zero`, `b_odd_eq_zero` — is reused verbatim;
* the conclusion is read at `m + (n + 1)`, which is odd exactly when `m` and `n` are both
  even.  `Even n` is the `p = 2` case of the programme's `p ∣ n`, and it is the only place
  the parity of the rank is used.

`ParityEven.lean` is not edited and not copied.

## Relation to `sp-evenside`'s mod-`p` even side

`CharClass/ParityPData.lean` proves the same conclusion generic in `p` *and* in the rank
(`ParityPData.gamma_rank_eq_zero`, `p ∣ n → p ∣ m → γ_{n+1+m} = 0`), and
`CharClass/ParityPTwo.lean` exhibits a `ParityData` as a `ParityPData 2`.  So
`gamma_top_rank_eq_zero` below is `P.toParityPData.gamma_rank_eq_zero` up to `add_comm` on
the index, and the two can be swapped without touching anything downstream: no statement in
this file or in `CharClass/LIXStepDGenData.lean` mentions `ParityData` or `ParityPData`.
This lane keeps the `F₂` route so that the rank-generic bridge does not depend on a lane in
flight; the index is written `m + (n + 1)` rather than `n + 1 + m` because that is the
shape whose `n = 2` instance is *definitionally* the landed `m + 3`.

## Main results

* `Gen.gamma_top_rank_eq_zero`, `Gen.gamma_top_rank_eq_zero_of_slice` — the abstract
  conclusion at rank `n`.
* `Gen.sphereClass` — the class pulled back from a sphere factor, in **any** degree.
* `Gen.sq_b_of_grading`, `Gen.tx_inj_of_degreewise` — the two Künneth/instability helpers
  at rank `n` (degree of `z` is `2n + 2`).
* `Gen.parityData_of` — the `ParityData` of the rank-`n` mapping torus.
* `Gen.gamma_top_eq_zero_of_slice_totalH`, `Gen.gamma_top_eq_zero_of_hasSplitting` —
  **the even side at rank `n`**: `γ_{m + n + 1}(W) = 0`.
* `Gen.gamma_top_eq_zero_of_hasSplitting_two` — the landed rank-two endpoint, re-derived.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Gen

noncomputable section

/-! ## 1. The abstract even side, read at the rank-`n` index -/

/-- **Step D's conclusion at rank `n`.**  The landed `ParityData.gamma_top_eq_zero` reads
the vanishing at `m + 3`; at rank `n` the top index is `m + (n + 1)`, and the argument is
the same one: `m + (n + 1)` is odd because `m` and `n` are even, so the `t x`-component
dies by `b_odd_eq_zero` and the `H^*(Y)`-component dies because the index is above the top
of the slice class.

`Even n` is the `p = 2` case of the programme note's `p ∣ n`; it is used here and nowhere
else. -/
theorem gamma_top_rank_eq_zero {R H : Type*} [CommRing R] [CommRing H] (P : ParityData R H)
    {n m : ℕ} (hn : Even n) (hm : Even m) (ha : ∀ q : ℕ, m < q → P.a q = 0) :
    P.γ (m + (n + 1)) = 0 := by
  have hodd : Odd (m + (n + 1)) := by
    obtain ⟨k, hk⟩ := hm
    obtain ⟨l, hl⟩ := hn
    exact ⟨k + l, by omega⟩
  rw [P.γ_eq (m + (n + 1)), ha (m + (n + 1)) (by omega), P.b_odd_eq_zero _ hodd,
    map_zero, mul_zero, add_zero]

/-- **Step D at rank `n`, packaged for the tower.**  If the slice class of `W` is
`∏_j (1 + h_j)^{d_j}` with every `d_j` even, then `γ_r(W) = 0` for `r = (∑_j d_j) + n + 1`.
Only evenness of the `d_j` and of the rank is used, never the tower's powers of two. -/
theorem gamma_top_rank_eq_zero_of_slice {R H : Type*} [CommRing R] [CommRing H]
    (P : ParityData R H) {n : ℕ} (hn : Even n)
    {J : Type*} (u : Finset J) (h : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, P.a q = (sliceClass u h d).coeff q) :
    P.γ ((∑ j ∈ u, d j) + (n + 1)) = 0 := by
  refine gamma_top_rank_eq_zero P hn (even_sum_of_forall_even d u hd) ?_
  intro q hq
  rw [hslice q, sliceClass_coeff_eq_zero_of_lt u h d hq]

/-! ## 2. The classes pulled back from the two sphere factors -/

variable {N Y S₁ Sodd : TopCat.{0}}

/-- **The class of `H^*(N)` pulled back from a sphere factor, in any degree.**  At degree
one this is `Wu.tClass` and at degree five `Wu.xClass`, both on the nose; at rank `n` the
odd sphere is `S^{2n+1}` and the degree is `2n + 1`, which is why the rank-two names cannot
be reused as they stand — their degree is pinned in the type of the generator. -/
def sphereClass {S : TopCat.{0}} (q : N ⟶ S) {c : ℕ} (σ : Hmod2 S c) : TotalH N :=
  TotalH.map q (TotalH.of S c σ)

theorem sphereClass_eq_tClass (q₁ : N ⟶ S₁) (σ₁ : Hmod2 S₁ 1) :
    sphereClass q₁ σ₁ = Wu.tClass q₁ σ₁ := rfl

theorem sphereClass_eq_xClass {S₅ : TopCat.{0}} (q₅ : N ⟶ S₅) (σ₅ : Hmod2 S₅ 5) :
    sphereClass q₅ σ₅ = Wu.xClass q₅ σ₅ := rfl

/-- The generator, as a class concentrated in its own degree. -/
theorem sphereClass_eq_of {S : TopCat.{0}} (q : N ⟶ S) {c : ℕ} (σ : Hmod2 S c) :
    sphereClass q σ = TotalH.of N c (pull q c σ) := TotalH.map_of q c σ

/-! ## 3. The two Künneth helpers at rank `n` -/

/-- **The instability field from the grading, at rank `n`.**  `z = t x` has degree
`2n + 2`, so the `z`-component `b k` of `γ_k` has degree `2k − (2n + 2)` and vanishes
outright below the total index `n + 1`.  This is `Wu.sq_b_of_grading` with the three
rank-two numbers replaced by their rank-`n` values; the owner of `hlow` and `hdeg` is the
Künneth layer (`cc-cohom-api`, then `sp-coeff`). -/
theorem sq_b_of_grading (n : ℕ) (b : ℕ → TotalH Y)
    (hlow : ∀ k : ℕ, k < n + 1 → b k = 0)
    (hdeg : ∀ k c : ℕ, 2 * k = c + (2 * n + 2) → ∃ β : Hmod2 Y c, b k = TotalH.of Y c β) :
    ∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0 := by
  intro k j hkj
  rcases Nat.lt_or_ge k (n + 1) with hk | hk
  · rw [hlow k hk, map_zero]
  · obtain ⟨β, hβ⟩ := hdeg k (2 * k - (2 * n + 2)) (by omega)
    rw [hβ]
    exact Steenrod.SqH_of_eq_zero_of_lt Y j (2 * k - (2 * n + 2)) (by omega) β

/-- **Künneth uniqueness at rank `n`, from the degreewise statement.**  The ring equation
splits into one equation per degree, and peeling the two generators one at a time reads, in
degree `1 + ((2n+1) + c)`, exactly the degreewise hypothesis at `c`.

The index is written `1 + ((2 * n + 1) + c)` rather than `2 * n + 2 + c` for the reason
`Wu.tx_inj_of_degreewise` gives at rank two: forming a single class of degree `2n + 2` out
of the two generators asks Lean for a definitional equality of cohomology groups that
unfolds the construction rather than reducing the index, and that exhausts the heartbeat
budget.  Peeling one generator at a time is cast-free. -/
theorem tx_inj_of_degreewise (n : ℕ) (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1))
    (h : ∀ (c : ℕ) (α : Hmod2 Y (1 + ((2 * n + 1) + c))) (β : Hmod2 Y c),
      pull p (1 + ((2 * n + 1) + c)) α
          + cup (pull q₁ 1 σ₁) (cup (pull qodd (2 * n + 1) σodd) (pull p c β)) = 0 → β = 0) :
    ∀ u v : TotalH Y,
      TotalH.map p u + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p v = 0 →
        v = 0 := by
  intro u v huv
  rw [mul_assoc, Wu.tClass_eq_of, sphereClass_eq_of] at huv
  ext c
  show TotalH.component Y c v = 0
  refine h c (TotalH.component Y (1 + ((2 * n + 1) + c)) u) (TotalH.component Y c v) ?_
  have hc := congrArg (TotalH.component N (1 + ((2 * n + 1) + c))) huv
  rw [map_add, map_zero, Wu.totalH_component_map, Wu.component_of_mul, Wu.component_of_mul,
    Wu.totalH_component_map] at hc
  exact hc

/-! ## 4. The even side at the rank-`n` objects -/

/-- **The `ParityData` of the rank-`n` mapping torus.**

`N` is the mapping torus base `S¹ × S^{2n+1} × Y`, `Y = ∏_j ℂP^{d_j}`, `p` the projection
to `Y`, and `q₁`, `qodd` the projections to the two sphere factors.  Every field that the
landed layers supply is proved by `ParityInstance.lean`'s rank-free lemmas — they are
already generic in the sphere's dimension — and the rest are hypotheses, one per field, as
at rank two.

`hsq_b` is asked for at the true rank-`n` degree of `b k`.  Since `2 ≤ n` makes
`6 ≤ 2n + 2`, it implies the `ParityData` field, whose bound is the rank-two one; that
implication is the only use of `hn2` and the only place where the rank-two shape of
`ParityEven.lean` shows through. -/
def parityData_of (n : ℕ) (hn2 : 2 ≤ n)
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (hS₁ : HasSphereCohomology S₁ 1) (hSodd : HasSphereCohomology Sodd (2 * n + 1))
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1))
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hcartan : ∀ (c : ℕ) (u v : TotalH N),
      Steenrod.SqH N c (u * v)
        = ∑ i ∈ Finset.range (c + 1), Steenrod.SqH N i u * Steenrod.SqH N (c - i) v)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k)
        + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p (b k))
    (ha_zero : a 0 = 1)
    (ha_odd : ∀ q : ℕ, Odd q → a q = 0)
    (hsq_b : ∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0)
    (hwu : ∀ i : ℕ, Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j)) :
    ParityData (TotalH Y) (TotalH N) where
  two_eq_zero := Wu.totalH_two_eq_zero Y
  ι := TotalH.map p
  t := Wu.tClass q₁ σ₁
  x := sphereClass qodd σodd
  t_mul_t := Wu.mul_self_pull_sphere_eq_zero q₁ hS₁ σ₁ (by omega)
  tx_inj := htx_inj
  SqH := Steenrod.SqH N
  SqR := Steenrod.SqH Y
  sqH_zero_apply := Steenrod.SqH_zero_apply N
  cartanH := hcartan
  sqH_t := fun c hc => Wu.sq_pull_sphere_eq_zero q₁ hS₁ σ₁ hc
  sqH_x := fun c hc => Wu.sq_pull_sphere_eq_zero qodd hSodd σodd hc
  sqH_ι := fun c r => Steenrod.SqH_map p c r
  γ := γ
  a := a
  b := b
  γ_eq := hγ
  a_zero := ha_zero
  a_odd := ha_odd
  sq_b := fun k j hkj => hsq_b k j (by omega)
  wu := hwu

@[simp] theorem parityData_of_gamma (n : ℕ) (hn2 : 2 ≤ n)
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (hS₁ : HasSphereCohomology S₁ 1) (hSodd : HasSphereCohomology Sodd (2 * n + 1))
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1))
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hcartan : ∀ (c : ℕ) (u v : TotalH N),
      Steenrod.SqH N c (u * v)
        = ∑ i ∈ Finset.range (c + 1), Steenrod.SqH N i u * Steenrod.SqH N (c - i) v)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k)
        + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p (b k))
    (ha_zero : a 0 = 1) (ha_odd : ∀ q : ℕ, Odd q → a q = 0)
    (hsq_b : ∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0)
    (hwu : ∀ i : ℕ, Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j)) (k : ℕ) :
    (parityData_of n hn2 p q₁ qodd hS₁ hSodd σ₁ σodd γ a b hcartan htx_inj hγ ha_zero
      ha_odd hsq_b hwu).γ k = γ k := rfl

/-- **Lemma 2, the even half, at rank `n`.**  Under the five hypotheses of
`parityData_of` — `a_zero` and `a_odd` are *not* among them, being consequences of the
slice class — the slice class `∏_j (1 + h_j)^{d_j}` with every `d_j` even, and `Even n`,
the top mod-2 Chern class of `W` vanishes in `H^*(N; F₂)`:
`γ_r(W) = 0` for `r = (∑_j d_j) + n + 1`. -/
theorem gamma_top_eq_zero_of_slice_totalH (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n)
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (hS₁ : HasSphereCohomology S₁ 1) (hSodd : HasSphereCohomology Sodd (2 * n + 1))
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1))
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hcartan : ∀ (c : ℕ) (u v : TotalH N),
      Steenrod.SqH N c (u * v)
        = ∑ i ∈ Finset.range (c + 1), Steenrod.SqH N i u * Steenrod.SqH N (c - i) v)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k)
        + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p (b k))
    (hsq_b : ∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0)
    (hwu : ∀ i : ℕ, Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j))
    {J : Type} (u : Finset J) (h : J → TotalH Y) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) :
    γ ((∑ j ∈ u, d j) + (n + 1)) = 0 :=
  gamma_top_rank_eq_zero_of_slice
    (parityData_of n hn2 p q₁ qodd hS₁ hSodd σ₁ σodd γ a b hcartan htx_inj hγ
      (Wu.a_zero_of_slice a u h d hslice) (Wu.a_odd_of_slice a u h d hd hslice) hsq_b hwu)
    hn u h d hd hslice

/-- **Lemma 2, the even half at rank `n`, from the `Prop`-valued splitting principle.**
The Cartan formula is quantified over the space (`Wu.CartanTotal`) and the diagonal Wu
relation comes from `Wu.HasSplitting`, exactly as at rank two; both are rank-free. -/
theorem gamma_top_eq_zero_of_hasSplitting (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n)
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (qodd : N ⟶ Sodd)
    (hS₁ : HasSphereCohomology S₁ 1) (hSodd : HasSphereCohomology Sodd (2 * n + 1))
    (σ₁ : Hmod2 S₁ 1) (σodd : Hmod2 Sodd (2 * n + 1))
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hC : Wu.CartanTotal)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k)
        + Wu.tClass q₁ σ₁ * sphereClass qodd σodd * TotalH.map p (b k))
    (hsq_b : ∀ k j : ℕ, 2 * k < j + (2 * n + 2) → Steenrod.SqH Y j (b k) = 0)
    (hsplit : Wu.HasSplitting N γ)
    {J : Type} (u : Finset J) (h : J → TotalH Y) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) :
    γ ((∑ j ∈ u, d j) + (n + 1)) = 0 :=
  gamma_top_eq_zero_of_slice_totalH n hn hn2 p q₁ qodd hS₁ hSodd σ₁ σodd γ a b
    (Wu.cartanH_of hC N) htx_inj hγ hsq_b (hsplit.wu hC) u h d hd hslice

/-! ## 5. The rank-two bridge

The landed rank-two endpoint is the `n = 2` instance of the generic one, and the statement
below is `Wu.gamma_top_eq_zero_of_hasSplitting` **verbatim** — the degrees `5` and `6` and
the top index `3` are what `2 * n + 1`, `2 * n + 2` and `n + 1` reduce to at `n = 2`, so no
cast, no `Equiv` and no re-proof stands between the two.  Nothing consumes this
declaration; it exists so that the subsumption is checked by the kernel rather than
asserted in a report. -/

theorem gamma_top_eq_zero_of_hasSplitting_two {S₅ : TopCat.{0}}
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hC : Wu.CartanTotal)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + Wu.tClass q₁ σ₁ * Wu.xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k) + Wu.tClass q₁ σ₁ * Wu.xClass q₅ σ₅ * TotalH.map p (b k))
    (hsq_b : ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0)
    (hsplit : Wu.HasSplitting N γ)
    {J : Type} (u : Finset J) (h : J → TotalH Y) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) :
    γ ((∑ j ∈ u, d j) + 3) = 0 :=
  gamma_top_eq_zero_of_hasSplitting 2 even_two le_rfl p q₁ q₅ hS₁ hS₅ σ₁ σ₅ γ a b hC
    htx_inj hγ hsq_b hsplit u h d hd hslice

end

end Gen
end CharClass
end GroupApproximation
