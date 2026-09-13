---
rg: 2
id: subshift-lef-models-period-below-twice-recurrence-proof
kind: route
title: Take the first recurrence of the initial 2k-word after position Rec(2k+1)-2k, and read the r-ball through windows of radius 2r
target: subshift-lef-models-period-below-twice-recurrence
requires: []
artifacts:
  - research/artifacts/sk-lef-short-proposal-2026-09-13.md
---

Direct proof. Conventions: `(Tx)_n = x_(n+1)`, `u f u^(-1) = f∘T^(-1)`, `P δ_n = δ_(n+1)`, and
`D_k(f) δ_n = f(T^n y_k) δ_n`. Recalled inputs: Morse–Hedlund `p_X(n) >= n+1` for infinite `X`, used only for
`N_k >= 2k+2` in item 2; Durand, used only for the example in item 3.

**Item 1.**
- Put `m = Rec_X(2k+1)`. Every word of length `2k` is a prefix of a word of length `2k+1`, since `X` consists of
  bi-infinite sequences. So `Rec_X(2k) <= m`.
- Fix `x ∈ X` and `v = x_[0,2k)`. The word `x_[m-2k, 2m-2k)` lies in `L_m(X)`, so it contains `v`, starting at some
  `N ∈ [m-2k, 2m-4k]`. For `k = 0`, `v` is empty and `N = m` works.
- Then `x_[0, N+2k)` begins and ends with `v`, so `x_i = x_(i-N)` for `i ∈ [N, N+2k)` and the word has period `N`.
  The `N`-periodic `y` with `y_[0,N) = x_[0,N)` agrees with `x` on `[0, N+2k)`.
- Every window of `y` of length `2k+1`, translated by a multiple of `N`, starts in `[0,N)` and ends by `N+2k-1`. So it
  is a subword of `x_[0,N+2k)`, a word of `X`.
- Conversely `x_[0,N+2k) ⊇ x_[0,m)`, which contains every word of `L_(2k+1)(X)`. So `L_(2k+1)(y) = L_(2k+1)(X)`.
- An `N`-periodic sequence has at most `N` windows of each length, so `N >= p_X(2k+1) >= 2k+2`.
- Finally `N <= 2m - 4k < 2m`.

**Item 2.**
- *Entries.* Let `V_t` be the `F_q`-span of the `f u^j` with `|j| <= t` and `f` depending only on coordinates in
  `[-t,t]`. A generator's entries lie in `V_1`. Multiplying by a generator changes an entry by a product with one more
  letter `λ s`. By `(f u^j) u^(±1) = f u^(j±1)` and `(f u^j) e_a = f (e_a∘T^(-j)) u^j`, the product has one more
  exponent unit and one more window coordinate. So all entries of `g ∈ B(r)` lie in `V_r`, and so do those of `g^(-1)`
  and of `g - h` for `g, h ∈ B(r)`.
- *Model.* Take `k = 2r` and `φ = φ_k`, `φ(Σ f_j u^j) = Σ D_k(f_j) P^j`. This is well defined and `F_q`-linear on
  `V_(2r)`, since windows of `y_k` of length `<= 4r+1` are words of `X`. For `a = f u^i` and `b = g u^j` in `V_r`,
  `ab = f·(g∘T^(-i)) u^(i+j)` has coefficient window inside `[-2r, 2r]`. `P^i D_k(g) P^(-i) = D_k(g∘T^(-i))` holds
  because `g∘T^(-i)` depends on coordinates in `[-2r,2r]`. So `φ(ab) = φ(a)φ(b)`.
- *Products.* Applied entrywise, `φ(gh) = φ(g)φ(h)` for all `g, h ∈ B(r)`. In particular `φ(g)φ(g^(-1)) = I`, so the
  images lie in `GL_(3N)(F_q)` with `N = N_(2r)`.
- *Injectivity.* If `g ≠ h`, some entry `Σ f_j u^j` of `g - h` is nonzero, with `|j| <= r`. Pick `f_j ≠ 0`, nonzero at
  a point whose `[-r,r]`-window lies in `L_(2r+1)(X)`. That word is a subword of a word in `L_(4r+1)(X) = L_(4r+1)(y_k)`,
  so `D_k(f_j) ≠ 0`. The term `D_k(f_j)P^j` is supported on the entries `(n+j, n)`. Distinct exponents with `|j| <= r`
  occupy disjoint entries because `N >= 4r+2 > 2r`. So `φ(g - h) ≠ 0`.
- *Bound.* `|GL_(3N)(F_q)| < q^(9N^2)` and `N < 2 Rec_X(4r+1)`.

**Item 3.** Substitute `Rec_X(4r+1) <= L(4r+1)`.

Model test: a finite (periodic) `X` fails the hypothesis, and item 1's lower bound `2k+2` fails for it. A Sturmian or
Fibonacci `X` has `Rec_X` linear, which gives `N = O(r)`.
