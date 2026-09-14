---
rg: 2
id: subshift-ring-isomorphism-preserves-soe-class-and-growth
kind: claim
title: If LC(X,F_2)⋊Z ≅ LC(Y,F_2)⋊Z as rings, for infinite minimal subshifts X and Y, then X and Y are strongly orbit equivalent and have equivalent complexity growth
distinct_from:
  cantor-crossed-product-matrix-ring-iso-forces-soe: that gives strong orbit equivalence from a matrix ring isomorphism; this adds the growth invariant, which strong orbit equivalence does not see
  subshift-crossed-product-algebraic-cartans-are-conjugate: that open claim would give flip conjugacy; this records the two ring invariants currently available, strong orbit equivalence class and complexity growth
---

Let `X, Y` be infinite minimal subshifts with word complexities `p_X, p_Y`. Put `R_X = LC(X,F_2) ⋊ Z` and similarly
`R_Y`, and suppose `R_X ≅ R_Y` as rings. Then:
1. `(X,T)` and `(Y,S)` are strongly orbit equivalent.
2. There is `C ≥ 1` such that, for all `n ≥ 1`,
   `⌊n/2⌋·p_Y(⌊n/2⌋) ≤ (2Cn+1)·p_X(2Cn)` and `⌊n/2⌋·p_X(⌊n/2⌋) ≤ (2Cn+1)·p_Y(2Cn)`.
3. `h_top(X) = 0` if and only if `h_top(Y) = 0`, and `h_top(Y) ≤ 4C·h_top(X)` and symmetrically.
4. `GKdim R_X = 1 + limsup_n log p_X(n)/log n`, so the upper polynomial exponent of complexity
   `limsup log p_X(n)/log n` is the same for `X` and `Y`.

So the algebraic crossed product over `F_2` carries at least the strong orbit equivalence class and the growth class of
the complexity function.
- Among all minimal homeomorphisms, entropy is not a strong orbit equivalence invariant. Boyle–Handelman, Pacific J.
  Math. 164 (1994), abstract: "Every minimal homeomorphism of a Cantor set is strongly orbit equivalent to a
  homeomorphism of zero entropy. The dyadic adding machine is strongly orbit equivalent to homeomorphisms of all
  entropies." (Read from the journal PDF, p. 1.)
- Whether one strong orbit equivalence class contains two expansive systems (subshifts) of zero and positive entropy is
  not checked here. So "ring isomorphism is strictly finer than strong orbit equivalence for subshifts" is not claimed.

Proof in `subshift-ring-isomorphism-soe-and-growth-proof`. It is a routine combination of Theorem R and Nekrashevych's
growth estimate. Neither gives flip conjugacy: see `subshift-crossed-product-algebraic-cartans-are-conjugate`.
