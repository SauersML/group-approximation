---
rg: 2
id: thompson-f-ore-window-kernel-profiles-proof
kind: route
title: Right multiplication by x_0 embeds window kernels forward, right multiples of one kernel vector fill a binomial count of each later window, and a never-settled pair has only zero windows
target: thompson-f-ore-window-kernel-profiles-monotone-binomial-floor
requires: []
artifacts:
  - research/artifacts/hl-f-kernel-profiles-2026-09-14.md
---

Notation as in the claim. `K[F]` has no zero divisors, since `F` is left-orderable (as used in
`thompson-f-p22-over-f2-census-exhaustive-proof`, Step 1). In particular right multiplication by a nonzero
element of `K[M]` is injective, and distinct normal forms are distinct elements of `M`.

**Step 0 (products of normal forms).** For normal forms `u` and `w`, the normal form of `u w` is obtained
by moving the letters of `w`, from left to right, to the left past every larger letter of the current word,
using `x_i x_j = x_j x_(i+1)` for `i > j`. Each step leaves the moving letter of `w` unchanged and increases
the passed letter by one. So in `u w`:
- the letters coming from `w` are unchanged;
- each letter coming from `u` increases by at most `deg w`.

**Item 1.** Let `(u, v) ∈ K[W_D]^2` with `a u = b v`. Then `a (u x_0) = b (v x_0)`. By Step 0 each letter
of `u` increases by at most one and the new letter `x_0` is unchanged, so `u x_0` and `v x_0` lie in
`K[M_(D+1, D+4)] = K[W_(D+1)]`. The map `(u, v) -> (u x_0, v x_0)` is linear and injective (no zero
divisors). So `k_D <= k_(D+1)`.

**Item 2.** Fix a nonzero `(u_0, v_0) ∈ K[W_δ]^2` with `a u_0 = b v_0`; by no zero divisors `u_0 ≠ 0`. For
`D >= δ` and `w ∈ M_(D − δ, D + 3)`, Step 0 shows that `u_0 w` has degree `D`, that its letters from `w`
are `<= D + 3`, and that its letters from `u_0` are `<= (δ + 3) + (D − δ) = D + 3`. The same holds for
`v_0 w`. So `(u_0 w, v_0 w) ∈ K[W_D]^2` and `a (u_0 w) = b (v_0 w)`. If `Σ_w c_w (u_0 w, v_0 w) = 0` then
`u_0 · (Σ_w c_w w) = 0`, hence `Σ_w c_w w = 0` and every `c_w = 0`. So these vectors are linearly
independent, and `k_D >= |M_(D − δ, D + 3)|`. A normal form of degree `n` with letters in `{0, ..., L}` is a
multiset of size `n` from `L + 1` letters, so `|M_(n, L)| = C(n + L, n)`; with `n = D − δ`, `L = D + 3`
this is `C(2D + 3 − δ, D − δ)`.

**Item 3.** `δ = ∞` means no nonzero common right multiple exists in any degree, so every `k_D = 0`. The
equivalence `δ = ∞ ⇔ k_D = 0 for all D` is Step 2 of `thompson-f-p22-over-f2-census-exhaustive-proof`
(letter windows suffice). A finite profile `k_0, ..., k_n` is therefore `0, ..., 0` for every pair with
`δ > n`, whether `δ` is finite or not, so it cannot distinguish a non-Ore pair from a pair settled in a
higher degree.

**Exact calibration.** `experiments/thompson-f/kprof/kprof.c` (exact `F_2` rank with singleton peeling and
sparse elimination), cross-checked against the independent `kprof_check.py` (bubble-rewrite normal forms,
plain elimination) for degrees `<= 5`, gives for the `S_(2,4)` pair `(1, 2)`:
`k_1..k_7 = 1, 6, 28, 120, 495, 2002, 8008 = C(2D+2, D−1)`, equality in item 2. Data in the artifact.
