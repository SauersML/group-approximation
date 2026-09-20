---
rg: 2
id: ledrappier-toeplitz-minimal-review
kind: claim
title: Referee review of 0d5291ca00 — the refutation of (FL) is correct; the F_4-twisted gaskets lie in the twisted Ledrappier shift, the 2-adic sum is locally finite and Toeplitz, the trace untwist lands in X_L with finite-index period lattices, and the point is not periodic, so Ledrappier's shift has an infinite (almost automorphic) minimal subset; odd-index Toeplitz points are periodic and 2-power ones are 0; no prior construction was found
distinct_from:
  ledrappier-shift-has-infinite-toeplitz-minimal-subsets: that is the lane node under review; this checks each step of the construction and of item 2.
  ledrappier-fl-reduction-review: that reviewed the reduction to (FL) and found (FL) open in the literature; this confirms its refutation.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the lane proof 0d5291ca00 by bh-bq2).** Verdict: **PASS.**
(FL) is false. The REFUTED flag on `ledrappier-shift-has-only-finite-minimal-subsets` is justified.

## Step 1: the gaskets lie in the twisted shift; correct

- **Coefficients of `ℓ^(N−1)`.** `N − 1` has `k+1` binary ones. The multinomial `binom(N−1; i, j, l)` is odd iff
  `i, j, l` have disjoint digits (Lucas–Kummer). With `j, l < N` disjoint, `i` is forced to be the complementary
  digits. So `ℓ^(N−1) = Σ ζ^(j+2l) X_1^j X_2^l` over disjoint `(j, l)`, with no wrap-around in `R_k`.
- **`ℓ^N = 0`.** By Frobenius, `ℓ^N = 1 + ζ^N X_1^N + ζ^(2N) X_2^N = 1 + ζ^N + ζ^(2N)` in `R_k`. This equals
  `1 + ζ + ζ^2 = 0`, whether `N ≡ 1` or `2 (mod 3)`.
- **The recursion.** The coefficient of `X^w` in `ℓ·ℓ^(N−1)` gives
  `G(w) + ζG(w−e_1) + ζ^2G(w−e_2) = 0`, with indices mod `N`. Substituting `w = (a_k,a_k) − v` gives
  `h_k ∈ X′`, and `h_k` is `NZ^2`-periodic.

## Step 2: local finiteness; correct

- **Supports.** `supp h_k` is the set of `v` for which the lowest `k+1` digits of `α − v_1` and `α − v_2` are
  disjoint, since `a_k ≡ α mod 2^(k+1)`.
- **The digit lemma.** Suppose `β` and `β + d` have disjoint digits, and `β` is not eventually constant.
  - Then `β` has infinitely many 0s and infinitely many 1s, so the carry or borrow of `2β + d` dies above some
    position `P`.
  - The no-carry sum makes `β` a submask of `2β + d`, whose digit `i` is digit `i − 1` of `β` for `i > P`.
  - So each 1 of `β` above `P` propagates down to `P`. Since there are infinitely many such 1s, all digits
    `≥ P` are 1, which is a contradiction.
  - Hence `β` is eventually constant, so rational.
- **Conclusion.** Since `α ∉ Q`, every `v` has a finite overlap position `p_v`, and the sum is locally finite.
  `X′` is linear and closed, so `x ∈ X′`.

## Step 3: Toeplitz; correct

- `H_K` depends only on `v mod 2^K` and contains every `supp h_k` with `k ≥ K`. Off `H_K`, `x` equals the
  `2^K`-periodic `p_K`, because `2^(k+1) | 2^K` for `k < K`.
- For a window with all `p_v < K`, the window and all of its `2^KZ^2`-translates avoid `H_K`, since the lowest `K`
  digits are unchanged. So `x` repeats along `2^KZ^2`.

## Step 4: the untwist lands in `X_L`; correct

- **The relation.** `ζ^(−1) = ζ^2` and `Tr` is `F_2`-linear. Hence
  `y(v) + y(v+e_1) + y(v+e_2) = Tr(ζ^(m(v))[x(v) + ζx(v+e_1) + ζ^2x(v+e_2)]) = 0`.
- **Periods.** `ζ^m` depends on `m mod 3`. So `y` repeats every window along
  `2^K{λ : λ_1 ≡ λ_2 mod 3}`, which has index `3·4^K`.
- **Minimality.** `y` is uniformly recurrent, so its orbit closure is minimal.

## Step 5: not periodic; correct

- **At `u`.** `β = α − u_0` has digits `0..P` equal to `0` and digit `P+1` equal to `1`. Both coordinates of `u`
  carry the same `β`. So `h_k(u) = G_k(0,0) = 1` for `k ≤ P`, and `h_k(u) = 0` for `k > P`.
- **At `u′`.** `β − 2^P n`, with `n` odd, has digits `0..P−1` equal to `0` and digit `P` equal to `1`. So
  `h_k(u′) = 0` for `k ≥ P`, and `h_k(u′) = h_k(u)` for `k < P`, by `2^(k+1)`-periodicity.
- **The difference.** `x(u) − x(u′) = ζ`. With `m(u) = m(u′) = 0`, this gives `y(u) − y(u′) = Tr(ζ) = ζ + ζ^2 = 1`.
- **Conclusion.** No nonzero multiple `2^Pn(1,1)` of `(1,1)` is a period, while every finite-index period lattice
  contains one. So `y` is not periodic, and its orbit closure is an **infinite minimal subset of `X_L`**.

## Item 2: correct

- **(a) Odd lattices are rigid.**
  - `q_λ = x + σ_λ x` vanishes on `c + Λ`, so it annihilates `u^cA_Λ`. With `N` odd, the separability argument
    of the homogeneous-form node gives `Frac(A_Λ) = F_2(s^N, t^N) = k`, so `A/u^cA_Λ` is finite.
  - The cocycle identity `q_(λ+μ) = q_λ + σ_λ q_μ` holds into the finite `Λ`-module `Q`. On the subgroup acting
    trivially on `Q` it is a homomorphism with finite-index kernel, so `x` is periodic.
  - A Toeplitz point is constant on a full coset of each of its period lattices, which gives the conclusion.
- **(b) 2-power Toeplitz points are `0`.** This holds in the stronger form: Frobenius gives
  `x(v + 2^Ke_2) = x(v) + x(v + 2^Ke_1)`, and on the `2^K`-skeleton the three values agree, so `x = 0` there.
  Every position eventually lies in a skeleton, so `x = 0`.
- **Wording.** "Mixing 2 and 3 is forced" is slightly too specific. What is forced is mixing 2 with **some odd
  prime**, and the example uses 3.

## Consistency with the Frobenius lemma (item 4 of the reduction node)

- **The odometer.** The maximal equicontinuous factor is the odometer `lim Z^2/2^K{λ_1 ≡ λ_2 mod 3}`, roughly
  `Z_2^2 × Z/3`.
- **The doubling orbit.** The images of `e_1, e_2` have mod-3 parts `±1`, and doubling alternates them between
  `1` and `2` and never reaches `0`. So `(0, 0)` is **not** an accumulation point of the doubling orbit. That is
  exactly the door the lemma left open, and the example uses it.

## Item 3 and T1: correct

- Toeplitz orbit closures are almost one-to-one extensions of odometers, hence proximal extensions.
- By the free-distal node (reviewed PASS), a T1 set is never a proximal extension of its maximal equicontinuous
  factor. So these sets cannot be T1 sets themselves.
- They can still be row projections of one. Algebraic T1 stays open, as stated.

## Priority check

- **Rowland–Yassawi, arXiv:1811.01256 (ar5iv).** They build nontrivial `(σ, Φ)`-invariant sets from automatic
  space-time diagrams, and do not address minimality. The present point is built from a non-rational 2-adic shift
  of the digit set, and need not be automatic.
- **Einsiedler 2004, as cited by Rowland–Yassawi.** Invariant sets of intermediate entropy, which are not
  zero-entropy Toeplitz sets.
- **Searches.** Queries on Ledrappier, Toeplitz, uniformly recurrent and minimal found no infinite minimal subset
  of Ledrappier's shift.
- **Conclusion.** No prior construction found, and no priority claimed, as in the node. As in my review of
  e85f22f6f9, the Einsiedler paper itself was not read in full.

## Bottom line

This is a correct and neat construction. Twisting by `ζ` turns the Frobenius obstruction into periodicity of the
Sierpinski gaskets. A non-rational 2-adic shift glues them into a Toeplitz point, and the trace untwist brings the
point back to `X_L`. (FL) is false. Algebraic T1 has to be decided in the non-almost-automorphic layers, as the
node says.
