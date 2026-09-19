---
rg: 2
id: minimal-z2-subshift-non-rf-iff-inside-aperiodic-sft-proof
kind: route
title: Uniform recurrence removes the covering clause, band pigeonhole upgrades one period to two, and the space-time subshift is minimal along its rows
target: minimal-z2-subshift-non-rf-iff-inside-aperiodic-sft
requires:
  - rf-subshifts-are-periodic-window-approximable
  - zn-subshift-is-rf-iff-periodically-approximable
  - commuting-subshift-automorphisms-die-when-space-time-is-rf
---

## Why sufficient

**Notation.**
- `Z^2` acts on configurations by `(g·c)(h) = c(h − g)`.
- For a finite `W ⊆ Z^2`, `L_W(Y) = {y|_W : y ∈ Y}`.
- `X_W(Y) = {c ∈ A^(Z^2) : (g^(-1)·c)|_W ∈ L_W(Y) for all g}` is the window SFT. It is an SFT and contains `Y`.
- If `W ⊆ W'`, then `X_(W')(Y) ⊆ X_W(Y)`, because a legal `W'`-window restricts to a legal `W`-window.
- `Y` is infinite and minimal, hence perfect, so `rf-subshifts-are-periodic-window-approximable` applies.

### Step 1: uniform recurrence

Fix a finite `W`. For `p ∈ L_W(Y)` and `R ≥ 0`, let
`U_(p,R) = {y ∈ Y : (g^(-1)·y)|_W = p for some g ∈ B_R}`.
- Each `U_(p,R)` is open.
- By minimality every orbit meets the cylinder of `p`, so `⋃_R U_(p,R) = Y`.
- By compactness `U_(p,R_p) = Y` for some `R_p`.

Let `R = max_p R_p`, which is finite because `L_W(Y)` is finite, and put `W' = W ∪ (W + B_R)`. Then every
`q ∈ L_(W')(Y)` contains every `p ∈ L_W(Y)`. Indeed, `q = y|_(W')` for some `y ∈ Y`, and `y` shows `p` on
`W + g` for some `g ∈ B_R`, with `W + g ⊆ W'`.

### Step 2: (a) ⇔ (b)

**If (b) fails, then Y is RF.**
- Fix a finite `W` and take `W'` from Step 1. Since (b) fails, `X_(W')(Y)` contains a point `c` with finite
  orbit. Let `O = Z^2·c`.
- `O` is finite and invariant, and `O ⊆ X_(W')(Y) ⊆ X_W(Y)`, so `{c'|_W : c' ∈ O} ⊆ L_W(Y)`.
- `c|_(W')` lies in `L_(W')(Y)`, so by Step 1 it contains every `p ∈ L_W(Y)` at some `W + g`. Then
  `(g^(-1)·c)|_W = p`, with `g^(-1)·c ∈ O`. So `{c'|_W : c' ∈ O} = L_W(Y)`.
- This holds for every `W`, so `Y` is RF by `rf-subshifts-are-periodic-window-approximable`.

**If Y is RF, then (b) fails.** By the same criterion, every `X_W(Y)` contains a finite invariant set `O`
whose `W`-windows are all of `L_W(Y)`. So `O` is nonempty, and any point of `O` has finite orbit.

### Step 3: one period gives two (b ⇔ c)

**(c) ⇒ (b).** In `Z^2`, a point with finite orbit has two independent periods, in particular a nonzero one.

**(b) ⇒ (c).** Let `Σ` be a `Z^2` SFT given by allowed patterns on a finite window `W_0`, and let `c ∈ Σ`
have a nonzero period `λ`. We show that `Σ` has a point with finite orbit.
- **Normalize.** Write `λ = k λ_0` with `λ_0` primitive and `k ≥ 1`, and extend `λ_0` to a basis
  `{λ_0, μ}` of `Z^2`. Let `α ∈ GL_2(Z)` send `e_1 ↦ λ_0` and `e_2 ↦ μ`. Then `c ∘ α` lies in the SFT
  with window `α^(-1)(W_0)` and has period `(k, 0)`. Finite orbits correspond under `α`. So we may assume
  `λ = (k, 0)`.
- **Bands.** Choose `h ≥ 1` greater than the vertical extent of `W_0`. Then every translate `W_0 + g`
  meets at most two consecutive bands `Z × [nh, (n+1)h)`. Let `R_n` be the band pattern
  `(i, j) ↦ c(i, nh + j)` for `0 ≤ j < h`.
- **Pigeonhole.** Each `R_n` is `k`-periodic in `i`, so it is determined by its restriction to
  `[0,k) × [0,h)`. There are at most `|A|^(kh)` possibilities, so `R_n = R_(n')` for some `n < n'`.
- **Repeat.** Put `P = (n' − n) h` and define `c'(i, nh + j) = c(i, nh + (j mod P))` for all `i, j ∈ Z`.
  Then `c'` repeats the bands `R_n, …, R_(n'−1)` vertically.
- **Legality.** A translate `W_0 + g` meets one or two consecutive bands of `c'`. These are either
  `(R_m, R_(m+1))` with `n ≤ m < n' − 1`, which occur consecutively in `c`, or the seam `(R_(n'−1), R_n)`.
  The seam equals `(R_(n'−1), R_(n'))`, which also occurs consecutively in `c`. So every `W_0`-window of `c'`
  is a `W_0`-window of `c`, and `c' ∈ Σ`.
- **Periods.** `c'` has the independent periods `(k, 0)` and `(0, P)`, so its orbit is finite.

Applied to `Σ = X_W(Y)`: if `X_W(Y)` has no finite orbit, it has no point with a nonzero period.

### Step 4: (c) ⇔ (d), and freeness

- **(c) ⇒ (d).** Take the SFT `X_W(Y)`. It contains `Y` and has no point with a nonzero period.
- **(d) ⇒ (a).** A strongly aperiodic SFT has no finite orbit, so this is item 2 of
  `zn-subshift-is-rf-iff-periodically-approximable`, equivalently `sfts-without-finite-orbits-are-not-residually-finite-actions`.
- **Freeness.** Under (c), `Y ⊆ X_W(Y)`, so no point of `Y` has a nonzero period. So `Y` is free.
- **The lemma on abelian actions.** For `g ∈ Λ`, the fixed set `Fix(g)` is closed. It is also
  `Λ`-invariant, because `h·Fix(g) = Fix(hgh^(-1)) = Fix(g)`. By minimality it is empty or everything, and
  it is everything exactly when `g` acts trivially.

This proves Theorem A.

### Step 5: the space-time subshift is minimal along its rows

Let `X` be infinite minimal, `ψ ∈ Aut(X,T)`, and `Φ(x)(m,n) = (ψ^n x)_m`, as in
`commuting-subshift-automorphisms-die-when-space-time-is-rf`. Step 0 of its proof gives
`Φ(Tx) = e_1-shift of Φ(x)`, and `Φ : X → Y_ψ` is a homeomorphism.
- **Minimality.** `(Y_ψ, e_1)` is conjugate to `(X, T)`, which is minimal. Hence `e_1` acts minimally, and
  `Y_ψ` is a minimal `Z^2`-subshift.
- **Expansiveness.** Row `0` of `Φ(x)` is `x`, and `x` determines `Φ(x)`. So two points of `Y_ψ` that agree
  on the strip `Z × {0}` around `R e_1` are equal, and `e_1` is an expansive direction.
- **Infinite order.** If `Y_ψ` is not RF, it is free by Theorem A. Since `(a,b) ∈ Z^2` acts on `X` as
  `T^a ψ^b`, freeness gives `T^a ψ^b ≠ id` for `(a,b) ≠ 0`. In particular `ψ^b ∉ ⟨T⟩` for every `b ≠ 0`.

### Step 6: Theorem B

- **(i) ⇒ (ii).** Let `Σ`, `Y'` and `v` witness (i). By item 2 of
  `zn-subshift-is-rf-iff-periodically-approximable`, `Y'` is not RF. By Theorem A, `Y'` is free.
  Theorem 4 of `commuting-subshift-automorphisms-die-when-space-time-is-rf` then gives `X` and `ψ` with
  `Y_ψ` conjugate to `Y'` after an automorphism of `Z^2`. Kerr–Nowak residual finiteness is invariant
  under conjugacy and under reparametrizing the acting group by an automorphism, since finite models are
  transported along both. So `Y_ψ` is not RF.
- **(ii) ⇔ (iii).** This is the negation of Theorem 1, (b) ⇔ (c), of
  `commuting-subshift-automorphisms-die-when-space-time-is-rf`, together with its remark that `(*)_F`
  for one block code of `ψ` gives it for all.
- **(ii) ⇒ (iv).** By Step 5, `Y_ψ` is minimal and `e_1` is expansive and minimal.
- **(iv) ⇒ (i).** Let `Y` witness (iv), with direction `v`. By Theorem A, `Y` lies in a `Z^2` SFT `Σ`
  without periodic points. `Y` is a minimal subsystem of `Σ`, and `v` is expansive and minimal on it.

### Step 7: Corollary C

Assume (i) fails. By Theorem B, (ii) fails, so every `Y_ψ` is RF. Theorem 1 of
`commuting-subshift-automorphisms-die-when-space-time-is-rf` then gives `(*)_F`, and its Theorem 2 kills
`(G2)` for every `σ` with `σ^m = Ad(w) ∘ σ_ψ^k`.

For the correction: by Step 5, `Y_ψ` is minimal. If it is not RF, Theorem A places it inside the
aperiodic SFT `X_W(Y_ψ)`.

## Audit

- Every step is elementary. Imported: the window criterion of `rf-subshifts-are-periodic-window-approximable`,
  item 2 of `zn-subshift-is-rf-iff-periodically-approximable`, and Theorems 1, 2 and 4 with Step 0 of
  `commuting-subshift-automorphisms-die-when-space-time-is-rf`.
- The band pigeonhole in Step 3 is the standard proof, recalled and written out here, that a singly
  periodic point of a `Z^2` SFT forces a doubly periodic one.
- **Where rank 2 is used.** Only in Step 3. In `Z^N` with `N ≥ 3`, Steps 1–2 still give "non-RF iff some
  window SFT is weakly aperiodic". The band argument does not give the upgrade to strong aperiodicity
  there, because a band with one period is no longer determined by finitely many values.
