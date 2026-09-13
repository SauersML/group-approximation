---
rg: 2
id: local-restricted-burnside-iff-partial-burnside-finite-quotients
kind: claim
title: A local restricted Burnside principle holds exactly when some partial Burnside group has only exponent-N finite quotients, and it forces non-residually-finite Coulon stages
distinct_from:
  restricted-burnside-finiteness: that is Zelmanov's theorem for finite groups satisfying the law on every element; this is the statement for finite groups satisfying the law only on words of bounded length, and its equivalences
  finite-nilpotent-groups-satisfy-local-restricted-burnside: that proves the local principle for finite nilpotent groups; this reformulates the principle for all finite groups, where it is open for large odd exponents
  hyperlinear-fg-bounded-exponent-groups-are-finite: that is the Hilbert--Schmidt finiteness principle for infinite groups of finite exponent; this concerns finite groups and exact laws on short words
---

**ESTABLISHED** through `local-restricted-burnside-partial-burnside-proof`.

**Setting.** Fix `m, N >= 2`, the free group `F = F_m` on `x_1, ..., x_m`, and
`R >= 1`. Let `N_R` be the normal closure in `F` of `{h^N : h in F, 1 <= |h| <= R}`
(reduced word length), and put `Π_R(m,N) = F / N_R`, the **partial Burnside
group** of radius `R`.

`LRB(R, C)` means: for every finite group `Q` and every generating tuple
`(s_1, ..., s_m)` of `Q` with `w(s)^N = 1` for all `w in F` with `|w| <= R`, we
have `|Q| <= C`. `LRB(m,N)` means `LRB(R, C)` for some `R` and `C`. This is the
statement called `LRB(m,N)` in Attempt 5 of
`hyperlinear-fg-bounded-exponent-groups-are-finite`.

**Statement.**
1. `LRB(R, C)` holds for some `C` iff `Π_R(m,N)` has only finitely many normal
   subgroups of finite index.
2. `LRB(R, C)` implies `LRB(R', C)` for every `R' >= R`.
3. `LRB(m,N)` holds iff there is `R*` such that every finite quotient of
   `Π_{R*}(m,N)` has exponent dividing `N`. For such `R*` the largest finite
   quotient of `Π_{R*}(m,N)` is the restricted Burnside group `R(m,N)`.
4. If `B(m,N)` is finite, `LRB(m,N)` holds.
5. Let `N` be odd with `N >= n_1(F_m)`, and let `G_k` be the non-elementary
   hyperbolic stages of `free-burnside-is-a-limit-of-hyperbolic-groups`.
   - If `LRB(m,N)` holds, then `G_k` is not residually finite for **every**
     sufficiently large `k`.
   - Conversely, if for every `k_0` some `G_k` with `k >= k_0` is residually
     finite, then `LRB(m,N)` fails. In particular, if every hyperbolic group is
     residually finite (a negative answer to
     `non-residually-finite-hyperbolic-group`), `LRB(m,N)` fails.

So `LRB(m,N)` for a large odd exponent is a sufficient condition for a
non-residually-finite hyperbolic group, and deciding it positively is at least
as hard as that root. No novelty is claimed.
