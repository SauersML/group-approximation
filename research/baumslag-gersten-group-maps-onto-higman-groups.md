---
rg: 2
id: baumslag-gersten-group-maps-onto-higman-groups
kind: claim
title: Killing the n-th power of the stable letter turns the Baumslag--Gersten group into Higman's group H_n extended by a cyclic group of order n
distinct_from:
  higman-group-satisfies-boone-higman: that is the open embedding question for Higman's group H4; this is an elementary quotient map linking BG to every Higman group H_n, with no embedding claim either way.
  baumslag-gersten-group-satisfies-boone-higman: that is the open embedding question for BG; this identifies the quotients BG/<<t^n>>, through which every homomorphism sending t to an element of order dividing n factors.
---

**ESTABLISHED** (lane proof, elementary Reidemeister--Schreier; not reviewed; no priority
claimed, very likely folklore).

## Statement

Let `BG = < a, t | b a b^-1 = a^2 >` with `b = t a t^-1`, and for `n >= 1` let

    H_n = < a_0, …, a_{n-1} | a_{i+1} a_i a_{i+1}^-1 = a_i^2  (indices mod n) >.

Then `BG / <<t^n>> ≅ H_n ⋊ C_n`, via `a ↦ a_0` and `t ↦` a generator `τ` of `C_n`, where `τ`
acts by `a_i ↦ a_{i+1}`. With `c_i = a_i^-1` the relations read `c_{i+1}^-1 c_i c_{i+1} = c_i^2`,
so `H_n` is Higman's group on `n` generators (up to reversing the cyclic order). In particular
`BG ↠ H_4 ⋊ C_4`, and the image of `a` has infinite order.

## Proof

Let `Q_n = < a, t | r, t^n >` with `r = (t a t^-1) a (t a t^-1)^-1 a^-2`, and let
`ε : Q_n → C_n` send `t ↦ τ` and `a ↦ 1`. Use the Schreier transversal `1, t, …, t^{n-1}`.
Reidemeister--Schreier gives, for `N = ker ε`:
- **Generators.** `a_i = t^i a t^{-i}` for `0 ≤ i < n`, and `γ_i = t^i · t · (t^{i+1 mod n})^-1`.
  Here `γ_i` is freely trivial for `i < n-1`, and `γ_{n-1} = t^n =: s`.
- **Relators.** Rewriting `t^i t^n t^{-i}` gives `s`. Rewriting `t^i r t^{-i}`, the path reads
  `t` (to the coset `t^{i+1}`), `a` (giving `a_{i+1}`), `t^-1`, `a` (giving `a_i`), `t`, `a^-1`,
  `t^-1`, `a^-2`, with each `t^{±1}` step contributing `s^{±1}` or nothing. Modulo `s = 1` it
  becomes `a_{i+1} a_i a_{i+1}^-1 a_i^-2`, indices mod `n`.

So `N ≅ H_n`. The map `ε` splits, because `t` has order exactly `n` in `Q_n`, and
`t a_i t^-1 = a_{i+1}` (for `i = n-1` this is `t^n a t^{-n} = a_0`). Hence `Q_n ≅ H_n ⋊ C_n`. ∎

**Cited, not re-read.** Higman (J. London Math. Soc. 26 (1951)): `H_4` is infinite, and each
`<a_i, a_{i+1}>` is `BS(1,2)` inside it (see also
`nontrivial-higman-quotients-keep-all-four-bs-subgroups`). `H_n` is trivial for `n ≤ 3`.

## Consequences

- **Small orders kill `a`.** If `ψ : BG → K` has `ψ(t)^n = 1` with `n ≤ 3`, then `ψ` factors
  through `H_n ⋊ C_n = C_n`, so `ψ(a) = 1`. For `n = 4` it can happen that `ψ(a)` has infinite
  order.
- **Finite quotients are cyclic** (Baumslag, 1969), recovered here. In a finite quotient,
  `ψ(t)` has some order `n`, so `ψ` factors through `H_n ⋊ C_n`, and `ψ(H_n)` is a finite
  quotient of `H_n`. That image is trivial by the classical argument, which needs no
  citation. The `x_i = ψ(a_i)` are conjugate, so they have a common order `m`, and
  `x_{i+1} x_i x_{i+1}^-1 = x_i^2` gives `x_i = x_i^{2^m}`, so `m | 2^m − 1` and `m` is odd. If `m > 1`, let `p` be its least prime
  factor. The order of `2` mod `p` divides `gcd(m, p − 1) = 1`, so `p | 2 − 1`, which is
  absurd. So `ψ(a) = 1` and the image is cyclic.
- **A bridge between two flagship test cases.** `BG` (BBMZ 5.3(9)) and `H4` (bh-testcases
  #1) are linked: `BG/<<t^4>>` contains `H_4`, with its four `BS(1,2)` subgroups intact.
  Embeddings do not pass to quotients, and quotients do not lift, so neither Boone--Higman
  question implies the other through this map. The link is structural. A host of `BG` in which
  a power `t^n`, `n ≥ 4`, acts trivially on some invariant piece carries a copy of an
  `H_n ⋊ C_n` quotient on that piece. If the piece is too small (`n ≤ 3`, or any finite
  piece), then `a` acts trivially there.
