---
rg: 2
id: houghton-ray-stabilizer-distortion-stack-sort-proof
kind: route
title: Split off the translation part, bound the support depth linearly, and realize the finitary part by three-stack merge sort
target: houghton-ray-stabilizer-distortion-at-most-x-log-x
requires: []
artifacts:
  - experiments/houghton-lid-transport-2026-09-17/check_lid_and_sort.py
  - experiments/houghton-lid-transport-2026-09-17/check_lid_and_sort.out
---

## Conventions

- These are the conventions of `houghton-h3-at-least-cubic-dehn-corridor-proof`.
- Points are `(r, q)` with `1 <= r <= n` and depth `q >= 1`.
- Permutations act on the right.
- `λ_(a,b)` sends `(a, 1) ↦ (b, 1)`, `(a, q) ↦ (a, q-1)` for `q >= 2` and
  `(b, q) ↦ (b, q+1)`. It fixes the other rays, and `λ_(a,b)^(-1) = λ_(b,a)`.
- `τ_r(h) ∈ Z` is the eventual translation of `h` on ray `r`. Each `τ_r` is a
  homomorphism.
- `K` is the pointwise stabilizer of ray `n`. For `a, b < n`,
  `λ_(a,b) ∈ K`, so each has bounded `S_K`-length. Let `c_K` bound the
  `S_K`-lengths of all `λ_(a,b)` with `a ≠ b < n`.

**Stack reading.** Regard ray `r` as a stack whose top is `(r, 1)`. Applying
`λ_(a,b)` pops the top point of stack `a` and pushes it onto stack `b`. After
a word `W` in these letters, the point that started at position `p` sits at
position `pW`. So any schedule of pops and pushes is a word, and it defines
the permutation "start position ↦ end position".

## Step 1. Support depth is linear in word length

Each `s ∈ S` agrees with a translation outside a finite set. Choose `c_1` so
that for `q > c_1` every `s ∈ S^(±1)` sends `(r, q) ↦ (r, q + τ_r(s))`. Put
`c_0 = max |τ_r(s)|`.

Let `W` be an `S`-word of length `ℓ` representing a finitary `σ`, so that all
`τ_r(σ) = 0`. Take a point `p = (r, q)` with `q > c_1 + c_0 ℓ`.

- After `j` letters, the image of `p` lies on ray `r` at depth
  `>= q - c_0 j > c_1`. So each letter moves it by its translation on ray `r`.
- Its final position is therefore `(r, q + Σ τ_r(letters)) = (r, q + τ_r(σ)) = p`.

So **`supp σ` lies in depth `<= D := c_1 + c_0 ℓ`.**

## Step 2. Three-stack merge sort

**Lemma.** Let `s, t, u` be three distinct rays. Let the top `N` points of
stack `s` carry distinct keys. There is a word `M` in `λ_(s,t), λ_(t,s),
λ_(s,u), λ_(u,s), λ_(t,u), λ_(u,t)` of length `T(N) <= 3 N ⌈log_2 N⌉` with
three properties:

- it reorders those `N` points so that the smallest key is on top, then the
  next smallest, and so on;
- every other point ends where it started;
- it never pops a point that is not among the `N` or pushed during `M`.

*Proof.* Induct on `N`. `N <= 1` is trivial with the empty word.

For `N >= 2`, put `h = ⌊N/2⌋` and do five things.

1. Move `h` points `s → t`, for `h` letters.
2. Sort them recursively on `t`, using `s` and `u` as auxiliaries.
3. Sort the remaining `N - h` points on `s`, using `t` and `u` as auxiliaries.
4. Merge. `N` times, pop the smaller of the two top keys of the halves on `s`
   and `t` and push it onto `u`. Each half is sorted with its minimum on top,
   so `u` receives keys in increasing order and ends with its maximum on top.
5. Move the `N` points `u → s`, for `N` letters. This reverses them, so the
   minimum is on top.

By induction, each recursive call leaves its two auxiliary stacks exactly as
it found them. Steps 4 and 5 pop only the points being sorted. So all other
points return to their places.

The cost satisfies `T(N) <= T(h) + T(N - h) + h + 2N`, and
`⌈log_2 ⌈N/2⌉⌉ = ⌈log_2 N⌉ - 1` for `N >= 2`. So by induction

`T(N) <= 3N(⌈log_2 N⌉ - 1) + 3N = 3N⌈log_2 N⌉`. ∎

**Corollary.** Let `σ` be a finitary permutation of rays `1..n-1` supported
in depth `<= D`, with `n - 1 >= 3`. Then `|σ|_(S_K) <= c_K (2(n-2)D + 3N⌈log_2 N⌉)`
with `N = (n-1)D`.

*Proof.*

- Let `G = Π_(r=2)^(n-1) λ_(r,1)^D`. It piles the top `D` points of every ray
  `r ∈ {2..n-1}` onto ray 1. `G` maps the depth-`<= D` region of rays
  `1..n-1` bijectively onto the top `N` positions of ray 1.
- So `σ^G = G^(-1) σ G` permutes the top `N` positions of ray 1 and fixes
  everything else.
- Key the point at position `(1, i)` by the depth of its `σ^G`-image. The
  Lemma, with `s = 1, t = 2, u = 3`, gives a word `M` realizing `σ^G`.
- Then `σ = G M G^(-1)`. ∎

This is the step that needs `n >= 4`. For `n = 3` the base has only two rays.

## Step 3. Translation part

Let `g ∈ K` with `|g|_S = ℓ`. Its translation vector `(τ_1(g), …, τ_(n-1)(g), 0)`
has sum zero and entries of size at most `c_0 ℓ`.

Put `t = Π_(j=2)^(n-1) λ_(1,j)^(τ_j(g))`. Then:

- `t ∈ K`, and `t` has the same translation vector as `g`;
- `|t|_(S_K) <= c_K (n-2) c_0 ℓ`;
- `|t|_S <= c' ℓ`.

So `σ = g t^(-1)` is finitary, has `|σ|_S <= (1 + c')ℓ`, and fixes ray `n`.

By Step 1, `σ` is supported in depth `D <= c_1 + c_0 (1 + c') ℓ`. By the
Corollary,

`|g|_(S_K) <= |σ|_(S_K) + |t|_(S_K) <= C (ℓ + 1) log(ℓ + 2)`. ∎

## Machine check

`check_lid_and_sort.py` part (4) runs for `n = 4, 5` and `D <= 34`:

- it builds `G M G^(-1)` for random finitary `σ` of depth `<= D`;
- it verifies the result equals `σ` as a permutation;
- it prints `|word| / (D log_2 D)`, which decreases from about 16–36 at small
  `D` to about 11–15 at `D = 34`, as expected for `Θ(D log D)`.

See `check_lid_and_sort.out`.
