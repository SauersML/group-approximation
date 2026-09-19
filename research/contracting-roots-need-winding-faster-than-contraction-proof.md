---
rg: 2
id: contracting-roots-need-winding-faster-than-contraction-proof
kind: route
title: A k-th root shifts the orbit of the path vertex by d = k^-1; a^-d r returns with section gamma = A_d^-1 beta_0 and gamma^k = h^e with gcd(e,k) = 1; bounded carries put (h, gamma) in a finite set that determines k; carries are sections of powers of length at most c_n and contract at rate rho_0
target: contracting-roots-need-winding-faster-than-contraction
requires:
  - contracting-groups-bound-roots-at-periodic-points
---

Lane proof (bh-free-16, 2026-09-19). Notation as in the claim. `O_n` is the `a`-orbit of `ξ_n`, of length `c_n`.

## Step 1. The root on the path orbit

Let `k` be `m`-free and `r ∈ Γ` with `r^k = a`.
- **The shift.** By Step 2 of `contracting-groups-bound-roots-at-periodic-points-proof`, `r` acts on level `n` as
  a power `a^(k')` with `kk' ≡ 1` modulo the order of `a` on that level. So `r` maps `O_n` to itself as the shift
  by `d`, where `0 <= d < c_n` and `dk ≡ 1 (mod c_n)`.
- **The returning element.** `u = a^-d r` fixes `ξ_n`. Since `(a^-d)|_(a^d ξ_n) = (a^d|_(ξ_n))^-1`, its section is
  ```
  γ := u|_(ξ_n) = A_d^-1 β_0,        β_0 = r|_(ξ_n).
  ```
- **The power relation.** `u` commutes with `a`, so `u^k = a^(−dk) r^k = a^(1−dk)`. Write `1 − dk = c_n e` with
  `e ∈ Z`. Then `a^(c_n e)` fixes `ξ_n` with section `h_n^e`, and `u` fixes `ξ_n`, so
  ```
  γ^k = h_n^e,     gcd(e, k) = 1     (since c_n e ≡ 1 mod k).
  ```
- **Commutation.** `γ` commutes with `h_n`, being a section at `ξ_n` of an element commuting with `a^(c_n)`,
  where both fix `ξ_n`.

## Step 2. The count (item 1)

- **The pair.** Choose `n` in the given infinite set with `n >= n(r)`, so that `β_0 ∈ 𝒩`. Then `h_n = A_(c_n) ∈ F`
  and `γ ∈ F^-1 𝒩`. So the pair `(h_n, γ)` lies in the finite set `F × F^-1 𝒩`, of size at most `|F|^2 |𝒩|`.
- **The pair determines `k`.** Suppose two orders `k, k'` give the same pair `(h, γ)`, with exponents `e, e'`.
  Then `h^(ek') = γ^(kk') = h^(e'k)`, and `h` has infinite order, so `ek' = e'k`. Since `gcd(e, k) = 1`, `k | k'`.
  By symmetry `k = k'`.

## Step 3. Carries contract (item 2)

- **Deep levels.** Iterating the contraction inequality, `|g|_v| <= λ^t |g| + C/(1 − λ)` for `|v| = tK`.
- **Intermediate levels.** For `|v| = tK + s` with `0 <= s < K`, sections at the remaining `s` levels multiply
  lengths by at most `M_0`, the largest length of a section of a generator at a level `< K`, raised to the power
  `K`. So `|g|_v| <= M(λ^t |g| + C')`.
- **The carries.** `A_j = a^j|_(ξ_n)` with `|a^j| <= j|a| <= c_n |a|` and `λ^t <= ρ_0^(n−K)`. This gives the
  stated bound, with `M` absorbing `ρ_0^-K`.
- **Bounded carries.** If `c_n ρ_0^n <= B` along a subsequence, all carries along it lie in a ball of radius
  `M(B|a| + C')`, which is a finite set `F`.

## Step 4. Items 3 and 4

- **Item 3.** `Z[1/P] ↪ Γ` with `1 ↦ a` gives `p`-th roots of `a` for infinitely many primes `p > m`. These `p`
  are `m`-free, so by item 1 the carries are unbounded along every good path, and by item 2
  `c_n ρ_0^n → ∞`.
- **Item 4.** In the product odometer, `a^j` is the translation by `(j, j)`. At `0^n` (level `n`) its section is the
  translation by `(⌊j/3^n⌋, ⌊j/2^n⌋)`, since the 3-adic digits carry past level `n` exactly `⌊j/3^n⌋` times, and
  likewise in the 2-adic factor. `c_n = 6^n`, as computed in the earlier node. Every section of a translation
  `(u, v)` at level `n` has size `<= |u|/3^n + 1` in the first coordinate and `<= |v|/2^n + 1` in the second. So the
  word metric of `Z^2` contracts at rate `1/2` per level, and `c_n ρ_0^n = 3^n → ∞`, consistent with the unbounded
  carries. ∎

## Remarks

- **Why carries.** A root has plain sections in the nucleus at deep levels. The only unbounded ingredient
  comparing it with `a` is the carry `A_d`, which is the section of the integer power `a^d` that transports `ξ_n`
  to `r(ξ_n)`. Bounded carries make `γ` bounded, and `γ` is a torsion-free `k`-th root datum. That is what the
  finite nucleus forbids for infinitely many `k`.
- **The periodic case.** If `c_n = c` is constant, the carries `a^j|_(ξ_n)`, `j <= c`, are plain sections of the
  finitely many elements `a^j`, eventually in `𝒩`. So item 1 contains `contracting-groups-bound-roots-at-periodic-points`,
  item 2, with `F = 𝒩` up to finitely many exceptions.
