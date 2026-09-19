---
rg: 2
id: houghton-ray-stabilizer-corridor-cap-proof
kind: route
title: Corridor certificates are at most x times the base distortion; lid transport and stack sort make the base nearly undistorted once it has three rays
target: houghton-ray-stabilizer-corridor-bounds-cap-near-quadratic
requires:
  - houghton-ray-stabilizer-distortion-at-most-x-log-x
artifacts:
  - experiments/houghton-lid-transport-2026-09-17/check_lid_and_sort.py
  - experiments/houghton-lid-transport-2026-09-17/check_lid_and_sort.out
---

The conventions are those of `houghton-ray-stabilizer-distortion-stack-sort-proof`:

- right actions;
- `λ_(a,b)` pops the top of ray `a` and pushes it onto ray `b`;
- `c_0, c_1, c_K` are the constants defined there;
- `S = S_K ∪ {Y}`.

Throughout, `n >= 4`.

## Step 0. The HNN presentation `P_n`

This is Step 1 of `houghton-h3-at-least-cubic-dehn-corridor-proof`, with `B`
replaced by `K` and ray 3 by ray `n`.

- **`φ(K) ⊆ K`.** For `h ∈ K`, the point `(n, q)` goes to `(n, q+1)` under
  `Y`, is fixed by `h`, and returns to `(n, q)` under `Y^(-1)`. So
  `Y h Y^(-1)` fixes ray `n`.
- **Generation.**
  - `K` contains every finitary permutation of rays `1..n-1`.
  - The elements `α^(Y^k)` swap adjacent points of the line
    `ray n ∪ ray 1` (fact F1 below).
  - Adjacent transpositions along a connected graph on all points generate
    `FSym`.
  - The translations of `K` span the sum-zero vectors supported on rays
    `1..n-1`, and `Y` adds `e_n - e_1`.
  - So `<K, Y> = H_n`.
- **Injectivity.** Every element of `K *_φ` is `t^(-a) b t^c` with `b ∈ K`.
  If it dies in `H_n`, then `c = a` (apply `τ_n`), so `b = 1`. This is
  verbatim 1b.
- **Finite presentation.** `H_n` is finitely presented for `n >= 3` (Lee,
  Corollary B, quoted in the cubic proof). By Neumann's theorem there is a
  finite set `R_0` of `Y`-free relators such that `P_n` presents `H_n`.

## Step 1. Corridors

This is Steps 2b–2c of the cubic proof, verbatim with `B → K`.

- Boundary `Y`-letters are paired by corridors, with opposite exponents.
- For a pair `(i, j)` with a corridor of `ℓ` cells, one side of the corridor
  is an `S_K`-word `U` of length `<= σ_P ℓ` with `U = w(i, j)` in `H_n`.
- Hence **`w(i, j) ∈ K`** (admissible) and **`ℓ >= |w(i, j)|_(S_K) / σ_P`**.

## Step 2. Claim (A): the class cap

Let `w` be null-homotopic with `|w| <= x`, and let `Δ` be any van Kampen
diagram for `w` (one exists). By Step 1, its corridor pairing `Π_Δ` is an
admissible pairing. So the certificate's minimum is at most its value on
`Π_Δ`.

`Π_Δ` has at most `x/2` pairs. Each arc is a subword of `w`, so it has
`S`-length `< x`, and it represents an element of `K`. Hence
`|arc|_(S_K) <= Dist_K(x)`, and

`bound(w) <= Σ_(Π_Δ) (A |arc|_(S_K) + B) <= (x/2)(A Dist_K(x) + B)`.

By `houghton-ray-stabilizer-distortion-at-most-x-log-x`,
`Dist_K(x) <= C x log x`. So `Cert(x) <= C' x^2 log x`. ∎

## Step 3. Claim (B): the forced family

Let `u` be an `S_K`-word and `m >= 2`. Put `g = Y^m u Y^(-m)` and

`W = g^(-1) α g α = Y^m u^(-1) Y^(-m) α Y^m u Y^(-m) α`,

with `|W| = 4m + 2|u| + 2`. Label its `Y`-letters `a_1..a_m`, `b_1..b_m`,
`c_1..c_m`, `d_1..d_m` by block, as in the cubic proof.

**Null-homotopy.** `(1, q) Y^m = (n, m+1-q)` for `q <= m`, and `u` fixes
ray `n`. So `g` fixes `(1,1)` and `(1,2)`, and it commutes with `α`.

**(F1).** For `k >= 1`, `(1,1) Y^k = (n, k)`. So `α^(Y^k)` moves `(n, k)`,
and `α^(Y^m) = ((n, m-1), (n, m))`.

The four opposite-sign cases, with `τ_n(arc) = 0` fixing the partner:

- **(i) `a_i` with `b_j`.** `j = m+1-i`, and the arc is `φ^k(u^(-1))` with
  `k = m - i`. It lies in `K`.
- **(ii) `a_i` with `d_j`.** `j - 1 = m - i =: k`, and the arc is
  `(u^(-1) α^(Y^m) u)^(Y^(-k))`. Since `u` fixes ray `n`, this is the
  transposition `α^(Y^m)` conjugated by `Y^(-k)`. It moves `(n, m-k)`, a
  ray-`n` point because `m - k >= 1`. **Inadmissible.**
- **(iii) `b_j` with `c_i`.** `i - 1 = m - j =: k`, and the arc is
  `α^(Y^k)`. By (F1) it is inadmissible unless `k = 0`, i.e. the pair
  `b_m`–`c_1` with arc `α`.
- **(iv) `c_i` with `d_j`.** `j = m+1-i`, and the arc is `φ^k(u)` with
  `k = m - i`.

**Forcing.** This is word for word the cubic proof.

- Each `a_i` must pair with a `Y^(-1)`, which by (ii) is not a `d`. So it is
  `b_(m+1-i)`, and this exhausts the `b`'s.
- Then each `c_i` pairs with `d_(m+1-i)`.

The certified value, with `F = |·|_(S_K)/σ_P`, is therefore

`V(W) = (1/σ_P) Σ_(k=0)^(m-1) (|φ^k(u^(-1))|_(S_K) + |φ^k(u)|_(S_K)) = (2/σ_P) Σ_(k<m) |φ^k(u)|_(S_K)`.

For `n = 3` and `u = X^m`, this is the cubic bound, since
`|φ^k(X^m)| >= inv = km`.

**Lid transport lemma (needs `n >= 4`).** Let `σ ∈ K` be finitary with
support in depth `<= D`, and let `k >= 0`. Choose distinct
`r, p ∈ {2, …, n-1}`; this is possible because `n - 1 >= 3`. Put

`z = λ_(r,p)^D λ_(r,1)^k λ_(p,r)^D ∈ K`.

Then `φ^k(σ) = z^(-1) σ z`.

*Proof.* In stack terms:

- the first factor parks the top `D` points of ray `r` on ray `p`;
- the second pops the next `k` points of ray `r` onto ray 1, which pushes
  every ray-1 point down by `k`;
- the third returns the parked points to ray `r`. They are reversed twice,
  so each lands in its original place.

So `z` fixes every point of depth `<= D` on rays `2..n-1` and sends
`(1, q) ↦ (1, q + k)`.

Now define `ψ` on rays `1..n-1` minus `F_k = {(1,1), …, (1,k)}` by
`(1, q) ↦ (1, q-k)`, and the identity on the other rays. `Y^k` acts as `ψ`
there and sends `F_k` into ray `n`, which `σ` fixes. So `φ^k(σ)`:

- fixes `F_k`;
- sends `s ψ^(-1) ↦ (s σ) ψ^(-1)` for every `s`;
- fixes every point outside `(supp σ) ψ^(-1)`.

`z` agrees with `ψ^(-1)` on the depth-`<= D` region, which contains
`supp σ`. So `z^(-1) σ z` has exactly the same description. ∎

**Translations (needs `n >= 4`).** For `j ∈ {2..n-1}`, `r ∈ {2..n-1} \ {j}`
and `a ∈ Z`:

`φ^k(λ_(1,j)^a) = λ_(r,1)^(-k) λ_(1,j)^a λ_(r,1)^k`.

*Proof.* `λ_(r,1)^(-k) = λ_(1,r)^k` sends `F_k` onto the top of ray `r`, acts
as `ψ` on the rest of ray 1, and pushes ray `r` down.

- `λ_(1,j)^a` fixes ray `r`.
- `λ_(r,1)^k` undoes the first map.

So both sides:

- fix `F_k` and ray `r`;
- act elsewhere as `p ↦ ((p ψ) λ_(1,j)^a) ψ^(-1)`. On the right side, the
  outer factors act as `ψ^(±1)` off ray `r ∪ F_k`, and `λ_(1,j)^a` never
  sends a point into ray `r`. On the left side this is the description of
  `φ^k` above. ∎

**Linear bound.** Let `|u| = ℓ`.

- Write `u = σ t` with `t = Π_j λ_(1,j)^(v_j)`, `|v_j| <= c_0 ℓ`, and `σ`
  finitary of depth `D <= c_1 + c_0(1 + c')ℓ` (Steps 1 and 3 of the
  distortion proof). Then `|σ|_(S_K) <= ℓ + |t|_(S_K) = O(ℓ)`.
- `φ^k` is a homomorphism, so
  `|φ^k(u)|_(S_K) <= |σ|_(S_K) + 2c_K(2D + k) + Σ_j c_K(|v_j| + 2k) <= C(ℓ + k + 1)`.

Therefore

`V(W) <= (2C/σ_P) Σ_(k<m) (ℓ + k + 1) <= C'(mℓ + m^2) <= C'' |W|^2`. ∎

**The kill, precisely.** Only one step differs from `n = 3`: bounding
`|φ^k(u)|_K` from below.

- For `n = 3`, `φ^k(X^m)` must move `k·m` inversions, because the lid
  `F_k` pins the top of the only other ray.
- For `n >= 4`, the lid can be parked on a spare ray at linear cost.

## Machine check

`check_lid_and_sort.out` records the following, for `n = 4, 5`:

- (1) `φ` maps each `λ_(a,b)` (`a, b < n`) and `α` into `K`;
- (2) the lid lemma, on 40 random finitary `σ` with `D <= 7`, `k <= 9`;
- (3) the translation identity, for all `j, r`, `|a| <= 4`, `k <= 6`;
- (5) the exact admissible-pair set for `W`, with random `u` of length
  `<= 8` and `m = 2..5`: exactly `a_i–b_(m+1-i)`, `c_i–d_(m+1-i)` and
  `b_m–c_1`.
