---
rg: 2
id: pure-braid-twist-depth-d-characters-lie-in-sigma-n-3-d
kind: claim
title: "A character of P_n whose zero twist types contain no laminar family larger than d <= n-4 lies in Sigma^{n-3-d}(P_n)"
distinct_from:
  pure-braid-nonzero-twist-characters-lie-in-sigma-n-minus-3: that claim is the case d = 0 (no vanishing twist value); this allows vanishing twist values and loses one level per curve in the largest zero multicurve.
  pure-braid-product-projections-obstruct-bnsr-invariants: that claim is an obstruction (characters outside Sigma^D); this is a membership criterion, exact on one strand block.
artifacts:
  - research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md
---

Let `n >= 4`, `chi = sum a_ij omega_ij != 0`, and `c_A(chi) = sum_{i<j in A} a_ij`.
Let `Z(chi)` be the family of zero types `A` (`2 <= |A| <= n - 1`, `c_A = 0`). The
twist depth `d(chi)` is the largest size of a laminar subfamily of `Z(chi)`
(any two members nested or disjoint), that is, the largest number of curves in a
multicurve of `D_n` on which `chi` vanishes. If `d = d(chi) <= n - 4`, then `[chi]`
lies in `Sigma^{n-3-d}(P_n)`.

Sharpness:

- Exact on one block. Let `A <= [n]` with `|A| >= 3`, and let `chi` be generic
  among the zero-sum characters supported on pairs inside `A`. Then
  `d(chi) = n - |A|`, so `[chi]` lies in `Sigma^{|A|-3} \ Sigma^{|A|-2}`. The upper
  bound is `pure-braid-product-projections-obstruct-bnsr-invariants` with `r = 1`.
  By `S_{n+1}`-symmetry this also covers the one-petal sunflower characters.
- Not sharp in general. On `P_5` with `c_12 = c_34 = 0` (generic otherwise, zero
  sum), `d = 2` and the criterion gives nothing, but `H^1` of the Aomoto complex
  vanishes, so the character is in `Sigma^1` by Koban–McCammond–Meier. Two
  disjoint zero-sum triples in `P_6` have `d = 3` and lie in `Sigma^1`.

Status: UNREVIEWED (swarm lane pure-braid-bnsr-complements, 2026-09-16).
