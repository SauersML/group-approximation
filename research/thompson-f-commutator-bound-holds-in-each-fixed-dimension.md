---
rg: 2
id: thompson-f-commutator-bound-holds-in-each-fixed-dimension
kind: claim
title: Unitary almost-solutions of F's relators obey a linear commutator bound in each fixed dimension, so nonhyperlinearity of F is boundedness of one monotone sequence
distinct_from:
  thompson-f-hyperlinear-iff-relator-system-hs-unstable: that is the dimension-uniform epsilon-delta equivalence; this proves the linear bound in every fixed dimension, identifies nonhyperlinearity with boundedness of the monotone limit of those constants, and forces witnesses into large irreducible degree.
  thompson-f-bounded-derived-length-pairs-obey-linear-bounds: that bounds pairs by the law their generated group satisfies; this bounds pairs by their matrix dimension, and neither class contains the other.
  thompson-f-is-not-residually-finite: that exhibits a nontrivial element in every finite-index normal subgroup; this uses that the finite residual is F' to get matrix estimates and to identify the representation schemes of F and Z^2.
artifacts:
  - research/artifacts/thompson-f-fixed-dimension-hs-bounds-2026-09-16.md
  - experiments/thompson-f-fixed-dimension-hs-constants-2026-09-16/inspect_witnesses.py
  - experiments/thompson-f-fixed-dimension-hs-constants-2026-09-16/replay_verify.py
---

**Statement.** Let `F = <a, b | R_1, R_2>` with `R_1 = [ab^-1, a^-1ba]` and `R_2 = [ab^-1, a^-2ba^2]`. For `U, W in U(n)` put
`delta(U,W) = max_i ||R_i(U,W) - I||_2`, in normalized Hilbert--Schmidt norm. Let `C_n(F)` be the least constant with

```text
||UW - WU||_2 <= C_n(F) delta(U,W)       for all U, W in U(n).
```

1. **Each dimension.** `C_n(F) < infinity` for every `n`, and `C_1(F) = 0`. The same holds with `[a,b]` replaced by
   any word with vanishing exponent sums.
2. **Schemes.** For every commutative ring `A`, every homomorphism `F -> GL_n(A)` has abelian image. Equivalently,
   the dimension-`n` relator ideal `J_n` (claim `profinite-kernel-words-have-fixed-dimension-hs-bounds`, item 1) of this
   presentation equals that of `Z^2 = <a, b | [a,b]>`. So `Rep_n(F) = Rep_n(Z^2)` as `Z`-schemes, and their cocycle
   spaces agree. No jet, deformation or tangent-space computation in bounded
   dimension separates `F` from `Z^2`.
3. **Reformulation.** `F` is not hyperlinear if and only if the nondecreasing sequence of algebraic numbers
   `C_1(F) <= C_2(F) <= ...` is bounded. If statement 3 of `thompson-f-hyperlinear-iff-relator-system-hs-unstable`
   holds at `epsilon = 1` with `delta`, then `sup_n C_n(F) <= 2/delta`.
4. **Degree escape.** `||UW - WU||_2^2 <= 2 C_D(F)^2 delta(U,W)^2 + 4 (1 - mu_D(U,W))`, where `mu_D` is the proportion of
   the dimension in irreducible summands of degree at most `D`. A hyperlinearity witness with commutator defect
   `||UW - WU||_2^2 >= epsilon` and `delta -> 0` eventually puts at least `epsilon/4` of the dimension in irreducible
   summands of degree greater than `D`, for every `D`.
5. **Lower bounds.** `C_2(F) >= 1 + sqrt 2`, attained by `U = diag(e^(3 pi i/8), e^(-3 pi i/8))` and
   `W = [[0,1],[-1,0]]`, where `c = U^2`, `R_1 = U^6` and `R_2 = U^10`. Also `C_n(F) >= 3.2286` for `n >= 4`, by a
   four-dimensional pair (numerically irreducible) with Gaussian-rational Cayley parameters. The inequality is verified in
   exact rational arithmetic. These are lower bounds only.

This does not decide `thompson-f-is-not-hyperlinear`. It shows that no fixed dimension, bounded irreducible degree, or
infinitesimal method can. Everything lies in the growth of `C_n(F)`.

Derivation: `thompson-f-fixed-dimension-commutator-bound-proof`.
