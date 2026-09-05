import GroupApproximation.CharClass.ParityEvenSlice

/-!
# Step D of the parity argument: the even side of Lemma 2

Let `N = S¹ × S⁵ × Y` with `Y = ∏_j CP^{d_j}` and every `d_j` even, let `W` be a
complex vector bundle on `N` whose restriction to the slice `{1} × S⁵ × Y` has
total mod-2 Chern class `∏_j (1 + h_j)^{d_j}`, and put `m = ∑_j d_j`,
`r = m + 3`.  Then `γ_r(W) = 0`.

## The mechanism

Künneth gives `H^*(N; F₂) = H_Y ⊕ t H_Y ⊕ x H_Y ⊕ t x H_Y` with `|t| = 1`,
`|x| = 5`, `t² = x² = 0`.  Only `H_Y` and `t x H_Y` sit in even degrees, so the
total mod-2 Chern class is `γ = a + t x b` with `a, b ∈ H_Y`; writing `a_k`, `b_k`
for the components with `γ_k = a_k + t x b_k`, the class `a_k` has degree `2k`
and `b_k` has degree `2k − 6`.

Apply (Wu-diag) at index `i`.  Because `Sq^{>0} t = Sq^{>0} x = 0`, the Cartan
formula gives `Sq^n (t x c) = t x Sq^n c`, so the `t x`-component of the relation
reads

```text
Sq^{2i}( b_{i+1} )  =  ∑_{j ≤ i} ( a_{i-j} b_{i+1+j} + b_{i-j} a_{i+1+j} ).
```

The left side vanishes **for free**: `b_{i+1}` has degree `2i − 4 < 2i`, so
instability kills it.  The right side, once both halves are reindexed by the
total index, is exactly the full convolution of `a` with `b` in odd total
degree.  So

```text
(★)   ∑_{q + k = N} a_q b_k = 0   for every odd N.
```

Now Frobenius: each `d_j` even makes the slice class a square, so `a_q = 0` for
every odd `q`, while `a_0 = 1`.  Reading (★) at an odd `N` by strong induction,
the `q = 0` term is `b_N`, the terms with `q` odd die because `a_q = 0`, and the
terms with `q ≥ 2` even have `N − q` odd and smaller, so they die by the
inductive hypothesis.  Hence `b_N = 0` for **every** odd `N`.  With `m` even,
`r = m + 3` is odd and `a_r = 0` above the top index, so `γ_r(W) = 0`.

## Departures from the design source

The route document (`stw59-obstruction-lean-routes-2026-09-05` §9) proves the
same conclusion by an induction on the number of projective factors, restricting
to sub-products, and for that it needs each `d_j` to be a **power of two** so
that each `a_q` is a single squarefree monomial.  The argument above never
restricts to a sub-product: it uses only that `a` is supported in even indices
and normalized.  So the power-of-two hypothesis is not needed, and `d_j` even
suffices, exactly as `notes/LIX_FULL_PROGRAM_2026-09-05.md` §1.3 states.  The
document's own index bookkeeping is also off by the shift between `b_n`
(indexed by its `H_Y`-degree halved) and `b_k` (indexed by the total index
`k = n + 3`); the version here uses the total index throughout, which is what
makes (★) come out as a plain convolution.

## Main results

* `GroupApproximation.CharClass.ParityData` — the hypotheses, as a structure.
* `ParityData.sum_a_mul_b_eq_zero` — the convolution identity (★).
* `ParityData.b_odd_eq_zero` — `b_N = 0` for every odd `N`.
* `ParityData.gamma_top_eq_zero` — `γ_{m+3}(W) = 0`.
* `ParityData.gamma_top_eq_zero_of_slice` — the same with the slice class of
  `ParityEvenSlice.lean` supplying the two hypotheses on `a`.
-/

namespace GroupApproximation.CharClass

open Finset

/-- The Künneth and Steenrod data of the mapping torus `N = S¹ × S⁵ × Y` that the
even side of Lemma 2 consumes.

`R` is `H^*(Y; F₂)` and `H` is `H^*(N; F₂)`; `a k` and `b k` are the two Künneth
components of the `k`-th mod-2 Chern class of the bundle.  Nothing here mentions
the rank of the bundle: the statement is rank-free. -/
structure ParityData (R H : Type*) [CommRing R] [CommRing H] where
  /-- The coefficients are `ZMod 2`. -/
  two_eq_zero : (2 : R) = 0
  /-- The Künneth inclusion `H^*(Y) → H^*(N)`. -/
  ι : R →+* H
  /-- The degree-one generator of `H^*(S¹)`. -/
  t : H
  /-- The degree-five generator of `H^*(S⁵)`. -/
  x : H
  /-- `t² = 0`, `t` being odd-dimensional. -/
  t_mul_t : t * t = 0
  /-- Künneth: the `t x`-component of the decomposition is well defined. -/
  tx_inj : ∀ u v : R, ι u + t * x * ι v = 0 → v = 0
  /-- Steenrod squares on `H^*(N)`. -/
  SqH : ℕ → H →+ H
  /-- Steenrod squares on `H^*(Y)`. -/
  SqR : ℕ → R →+ R
  /-- `Sq^0` is the identity. -/
  sqH_zero_apply : ∀ c : H, SqH 0 c = c
  /-- The Cartan formula on `H^*(N)`. -/
  cartanH : ∀ (n : ℕ) (u v : H),
    SqH n (u * v) = ∑ p ∈ Finset.range (n + 1), SqH p u * SqH (n - p) v
  /-- `t` is pulled back from `S¹`, whose cohomology vanishes above degree one. -/
  sqH_t : ∀ n : ℕ, 0 < n → SqH n t = 0
  /-- `x` is pulled back from `S⁵`, whose cohomology vanishes above degree five. -/
  sqH_x : ∀ n : ℕ, 0 < n → SqH n x = 0
  /-- `Sq` preserves the Künneth decomposition. -/
  sqH_ι : ∀ (n : ℕ) (r : R), SqH n (ι r) = ι (SqR n r)
  /-- The mod-2 Chern classes of `W`. -/
  γ : ℕ → H
  /-- The `H_Y`-component of `γ k`, of degree `2k`. -/
  a : ℕ → R
  /-- The `t x H_Y`-component of `γ k`, of degree `2k − 6`. -/
  b : ℕ → R
  /-- The Künneth decomposition of the Chern classes. -/
  γ_eq : ∀ k : ℕ, γ k = ι (a k) + t * x * ι (b k)
  /-- `γ 0 = 1`. -/
  a_zero : a 0 = 1
  /-- Frobenius evenness of the slice class: it is a square, so its odd-index
  components vanish.  `sliceClass_coeff_odd_eq_zero` produces this. -/
  a_odd : ∀ q : ℕ, Odd q → a q = 0
  /-- Instability, in the only form used: `b k` has degree `2k − 6` in `H^*(Y)`,
  so `Sq^j` kills it as soon as `j` exceeds that degree. -/
  sq_b : ∀ k j : ℕ, 2 * k < j + 6 → SqR j (b k) = 0
  /-- The diagonal Wu relation for the classes `γ`. -/
  wu : ∀ i : ℕ, SqH (2 * i) (γ (i + 1))
    = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j)

namespace ParityData

variable {R H : Type*} [CommRing R] [CommRing H] (P : ParityData R H)

/-! ### Elementary consequences of the structure -/

theorem two_eq_zero_target : (2 : H) = 0 := by
  have hh : (2 : H) = P.ι 2 := by simp
  rw [hh, P.two_eq_zero, map_zero]

theorem sqH_mul_t (n : ℕ) (u : H) : P.SqH n (P.t * u) = P.t * P.SqH n u := by
  rw [P.cartanH n P.t u,
    Finset.sum_eq_single 0
      (fun p _ hp => by rw [P.sqH_t p (Nat.pos_of_ne_zero hp), zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h),
    P.sqH_zero_apply, Nat.sub_zero]

theorem sqH_mul_x (n : ℕ) (u : H) : P.SqH n (P.x * u) = P.x * P.SqH n u := by
  rw [P.cartanH n P.x u,
    Finset.sum_eq_single 0
      (fun p _ hp => by rw [P.sqH_x p (Nat.pos_of_ne_zero hp), zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h),
    P.sqH_zero_apply, Nat.sub_zero]

/-- `Sq^n` acts on the `t x`-component through `Sq^n` on `H^*(Y)`. -/
theorem sqH_tx_mul (n : ℕ) (r : R) :
    P.SqH n (P.t * P.x * P.ι r) = P.t * P.x * P.ι (P.SqR n r) := by
  rw [mul_assoc, P.sqH_mul_t, P.sqH_mul_x, P.sqH_ι, ← mul_assoc]

theorem tx_mul_tx : P.t * P.x * (P.t * P.x) = 0 := by
  have h : P.t * P.x * (P.t * P.x) = P.t * P.t * (P.x * P.x) := by ring
  rw [h, P.t_mul_t, zero_mul]

/-- The product of two Chern classes, read through the Künneth decomposition. -/
theorem gamma_mul (m n : ℕ) :
    P.γ m * P.γ n
      = P.ι (P.a m * P.a n)
        + P.t * P.x * P.ι (P.a m * P.b n + P.b m * P.a n) := by
  rw [P.γ_eq m, P.γ_eq n]
  have expand :
      (P.ι (P.a m) + P.t * P.x * P.ι (P.b m)) * (P.ι (P.a n) + P.t * P.x * P.ι (P.b n))
        = P.ι (P.a m) * P.ι (P.a n)
          + P.t * P.x * (P.ι (P.a m) * P.ι (P.b n) + P.ι (P.b m) * P.ι (P.a n))
          + P.t * P.x * (P.t * P.x) * (P.ι (P.b m) * P.ι (P.b n)) := by ring
  rw [expand, P.tx_mul_tx, zero_mul, add_zero]
  simp only [map_mul, map_add]

/-! ### The convolution identity -/

/-- **The `t x`-component of (Wu-diag).**  For every `i`, the convolution of `a`
with `b` vanishes in the odd total index `2i + 1`. -/
theorem sum_a_mul_b_eq_zero (i : ℕ) :
    ∑ q ∈ Finset.range (2 * i + 1 + 1), P.a q * P.b (2 * i + 1 - q) = 0 := by
  set A : R := ∑ j ∈ Finset.range (i + 1), P.a (i - j) * P.a (i + 1 + j) with hA
  set B : R := ∑ j ∈ Finset.range (i + 1),
    (P.a (i - j) * P.b (i + 1 + j) + P.b (i - j) * P.a (i + 1 + j)) with hB
  have hlhs : P.SqH (2 * i) (P.γ (i + 1)) = P.ι (P.SqR (2 * i) (P.a (i + 1))) := by
    rw [P.γ_eq (i + 1), map_add, P.sqH_ι, P.sqH_tx_mul,
      P.sq_b (i + 1) (2 * i) (by omega), map_zero, mul_zero, add_zero]
  have hrhs : ∑ j ∈ Finset.range (i + 1), P.γ (i - j) * P.γ (i + 1 + j)
      = P.ι A + P.t * P.x * P.ι B := by
    rw [hA, hB, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => P.gamma_mul _ _
  have hL : P.ι (P.SqR (2 * i) (P.a (i + 1))) = P.ι A + P.t * P.x * P.ι B := by
    rw [← hlhs, P.wu i, hrhs]
  have hzero : P.ι (P.SqR (2 * i) (P.a (i + 1)) + A) + P.t * P.x * P.ι B = 0 := by
    rw [map_add, hL]
    have hsum : P.ι A + P.t * P.x * P.ι B + P.ι A + P.t * P.x * P.ι B
        = (P.ι A + P.t * P.x * P.ι B) + (P.ι A + P.t * P.x * P.ι B) := by ring
    rw [hsum]
    exact add_self_eq_zero_of_two_eq_zero P.two_eq_zero_target _
  have hkey : B = 0 := P.tx_inj _ B hzero
  -- Reindex both halves of `B` by the total index.
  have hB1 : ∑ j ∈ Finset.range (i + 1), P.a (i - j) * P.b (i + 1 + j)
      = ∑ q ∈ Finset.range (i + 1), P.a q * P.b (2 * i + 1 - q) := by
    have key : ∀ j ∈ Finset.range (i + 1),
        P.a (i - j) * P.b (i + 1 + j)
          = (fun q => P.a q * P.b (2 * i + 1 - q)) (i + 1 - 1 - j) := by
      intro j hj
      have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have e1 : i + 1 - 1 - j = i - j := by omega
      have e2 : 2 * i + 1 - (i - j) = i + 1 + j := by omega
      simp only [e1, e2]
    rw [Finset.sum_congr rfl key, Finset.sum_range_reflect]
  have hB2 : ∑ j ∈ Finset.range (i + 1), P.b (i - j) * P.a (i + 1 + j)
      = ∑ q ∈ Finset.range (i + 1), P.a (i + 1 + q) * P.b (2 * i + 1 - (i + 1 + q)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show 2 * i + 1 - (i + 1 + j) = i - j from by omega, mul_comm]
  rw [show 2 * i + 1 + 1 = i + 1 + (i + 1) from by omega,
    Finset.sum_range_add (fun q => P.a q * P.b (2 * i + 1 - q)) (i + 1) (i + 1),
    ← hB1, ← hB2, ← Finset.sum_add_distrib, ← hB]
  exact hkey

/-! ### The vanishing of the odd part of `b` -/

/-- **The even side.**  Every odd-index Künneth component `b N` vanishes. -/
theorem b_odd_eq_zero : ∀ N : ℕ, Odd N → P.b N = 0 := by
  suffices H' : ∀ M N : ℕ, N ≤ M → Odd N → P.b N = 0 by
    intro N hN
    exact H' N N le_rfl hN
  intro M
  induction M with
  | zero =>
    intro N _ hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  | succ M ihM =>
    intro N hNM hodd
    obtain ⟨i, hi⟩ := hodd
    subst hi
    have hconv := P.sum_a_mul_b_eq_zero i
    rw [Finset.sum_range_succ' (fun q => P.a q * P.b (2 * i + 1 - q)) (2 * i + 1)] at hconv
    have hz : ∑ q ∈ Finset.range (2 * i + 1), P.a (q + 1) * P.b (2 * i + 1 - (q + 1)) = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      have hq' : q < 2 * i + 1 := Finset.mem_range.mp hq
      rcases Nat.even_or_odd (q + 1) with he | ho
      · obtain ⟨m, hm⟩ := he
        have hodd' : Odd (2 * i + 1 - (q + 1)) := ⟨i - m, by omega⟩
        rw [ihM (2 * i + 1 - (q + 1)) (by omega) hodd', mul_zero]
      · rw [P.a_odd (q + 1) ho, zero_mul]
    rw [hz, zero_add, Nat.sub_zero, P.a_zero, one_mul] at hconv
    exact hconv

/-! ### The conclusion -/

/-- **Step D.**  If `m` is even and the slice class vanishes above index `m`, then
the top mod-2 Chern class `γ_{m+3}(W)` vanishes. -/
theorem gamma_top_eq_zero {m : ℕ} (hm : Even m) (ha : ∀ q : ℕ, m < q → P.a q = 0) :
    P.γ (m + 3) = 0 := by
  obtain ⟨k, hk⟩ := hm
  have hodd : Odd (m + 3) := ⟨k + 1, by omega⟩
  rw [P.γ_eq (m + 3), ha (m + 3) (by omega), P.b_odd_eq_zero (m + 3) hodd,
    map_zero, map_zero, mul_zero, add_zero]

/-- **Step D, packaged for the tower.**  If the slice class of `W` is
`∏_j (1 + h_j)^{d_j}` with every `d_j` even, then `γ_r(W) = 0` for
`r = (∑_j d_j) + 3`. -/
theorem gamma_top_eq_zero_of_slice {J : Type*} (u : Finset J) (h : J → R) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, P.a q = (sliceClass u h d).coeff q) :
    P.γ ((∑ j ∈ u, d j) + 3) = 0 := by
  refine P.gamma_top_eq_zero (even_sum_of_forall_even d u hd) ?_
  intro q hq
  rw [hslice q, sliceClass_coeff_eq_zero_of_lt u h d hq]

end ParityData

end GroupApproximation.CharClass
