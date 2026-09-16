---
rg: 2
id: pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3
kind: claim
title: "A character of P_n that is nonzero on every Dehn twist of the punctured disk lies in Sigma^{n-3}(P_n)"
distinct_from:
  pure-braid-top-bnsr-invariants-are-center-nonvanishing: that claim uses only the full twist (the boundary twist) and settles Sigma^m for m >= n-2; this uses the twists about all essential curves and gives Sigma^{n-3} for zero-sum characters, which that claim puts outside Sigma^{n-2}.
  pure-braid-bns-invariant-is-circle-complement: that claim computes Sigma^1 only; this is a sufficient condition in degree n-3, which for n = 4 is compatible with it (every KMM circle lies on a twist hyperplane).
artifacts:
  - research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md
---

Let `n >= 4` and `chi = sum_{i<j} a_ij omega_ij` in winding-number coordinates. For
`A <= [n]` let `c_A(chi) = sum_{i<j in A} a_ij`. This is the value of `chi` on the
Dehn twist about a curve in `D_n` that surrounds the punctures `A`. If
`c_A(chi) != 0` for every `A` with `2 <= |A| <= n - 1`, then `[chi]` lies in
`Sigma^{n-3}(P_n)`.

Consequences:

- With `pure-braid-top-bnsr-invariants-are-center-nonvanishing`: if moreover
  `sum a_ij = 0`, then `[chi]` is in `Sigma^{n-3}(P_n) \ Sigma^{n-2}(P_n)`.
- This contains the positive half of Zaremsky, arXiv:1507.08597, Proposition 5.6
  (zero sum, exactly one positive or exactly one negative coefficient, no zero
  coefficient). It also covers characters with several coefficients of each sign.
- In degrees `2 <= m <= n - 3`, the non-resonant-implies-`Sigma^m` direction of
  `pure-braid-bnsr-complements-are-real-resonance-varieties` holds off the
  finitely many twist hyperplanes `c_A = 0`.

Status: UNREVIEWED (swarm lane pure-braid-bnsr-complements, 2026-09-16).
