---
rg: 2
id: serre-class-atoms-degree-bound-proof
kind: route
title: Box principle - an integer polynomial of degree below deg x that is tiny at an atom x makes the Serre integral negative when the atom is heavy
target: serre-class-atoms-obey-degree-bound
requires: []
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

Artifact Section 2. Let `mu` be supported in `[-C, C]`, `C >= 1`, with an atom
`w = mu({x}) > 0`, and fix an integer `N >= 1` with `N < deg(x)`.

1. **Box principle.** For an integer `H >= 1`, the `(H+1)^(N+1)` vectors
   `a in {0..H}^(N+1)` give values `sum_(i<=N) a_i x^i` in an interval of
   length `H s`, where `s = sum_(i<=N) |x|^i <= (N+1) C^N`. Cut it into
   `(H+1)^(N+1) - 1 >= H^(N+1)` equal pieces. Two distinct vectors share a
   piece, and their difference is a nonzero `Q in Z[x]` with `deg Q <= N`,
   coefficients bounded by `H`, and `|Q(x)| <= s H^(-N)`.
2. **`Q(x) != 0`,** since `deg Q < deg(x)`.
3. **Sup bound.** On `[-C, C]`, `|Q| <= B_H = (N+1) H C^N`, and `B_H >= 1`.
4. **Estimate.** The atom contributes `w log|Q(x)| <= w log s - w N log H`.
   The rest of `{Q != 0}` has mass at most `1 - w` and integrand at most
   `log B_H >= 0`. So

   ```text
   0 <= integral_(Q != 0) log|Q| d mu
     <= -(w(N+1) - 1) log H + w log s + (1-w) log((N+1) C^N).
   ```
5. **Conclusion.** Letting `H -> infinity` forces `w (N+1) <= 1`.
   - For `deg(x) = d` finite, `N = d - 1` gives `w <= 1/d`.
   - For transcendental `x`, `N` is arbitrary, so `w = 0`. QED
