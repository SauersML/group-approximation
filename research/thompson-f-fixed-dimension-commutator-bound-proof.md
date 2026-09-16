---
rg: 2
id: thompson-f-fixed-dimension-commutator-bound-proof
kind: route
title: The finite residual of F is F', so the ideal-membership bound applies to the commutator in each dimension, and the dimension-free gap turns the limit into the root
target: thompson-f-commutator-bound-holds-in-each-fixed-dimension
requires:
  - profinite-kernel-words-have-fixed-dimension-hs-bounds
  - thompson-f-hyperlinear-iff-relator-system-hs-unstable
  - fixed-hs-word-gap-is-linear-domination
artifacts:
  - research/artifacts/thompson-f-fixed-dimension-hs-bounds-2026-09-16.md
  - experiments/thompson-f-fixed-dimension-hs-constants-2026-09-16/inspect_witnesses.py
  - experiments/thompson-f-fixed-dimension-hs-constants-2026-09-16/replay_verify.py
---

Full proofs: artifact, Sections 3 and 4. Numbering follows the claim. `c = [a,b]`, and `||UW - WU||_2 = ||c(U,W) - I||_2`
by bi-invariance.

**Import (trust surface).** Every proper quotient of `F` is abelian (Cannon--Floyd--Parry 1996). It is pinned as a quotation
in `thompson-f-is-lea-only-if-amenable-proof` and used the same way in `thompson-f-verbal-commutator-bounds-proof`.

**0. Finite residual.** `F` is infinite, so every finite quotient is proper, hence abelian, and kills `F'`. `R_1, R_2` are
commutators, so `F/F' = Z^2`, which is residually finite, and the finite residual of `F` is exactly `F'`. A word maps into `F'`
exactly when its exponent sums vanish.

**1. Each dimension.** By step 0, `c` (and every word with vanishing exponent sums) is profinitely trivial in `F`. Item 2 of
`profinite-kernel-words-have-fixed-dimension-hs-bounds` gives `C_n(F) <= 2 n^2 L_n < infinity`. `U(1)` is abelian, so
`C_1(F) = 0`.

**2. Schemes.** Item 1 of `profinite-kernel-words-have-fixed-dimension-hs-bounds`, applied to `c`, puts the entries of
`c(X) - I` in `J_n(R_1, R_2)`. Conversely, over `B_0/J_n(c)` the universal representation factors through `Z^2`, so it kills
the commutators `R_1, R_2`, and their entries lie in `J_n(c)`. `B_0/J_n` represents `A -> Hom(-, GL_n(A))` on commutative
rings, so the functors agree and every `F -> GL_n(A)` has abelian image. Tangent spaces at `rho` are the cocycle spaces
`Z^1(-, M_n(K)_(Ad rho))`, read off from `K[epsilon]/(epsilon^2)`-points, so they agree. For jets, apply the functor
statement to `A = C[[t]]/(t^k)`.

**3. Reformulation.** Monotonicity is item 4 of the general claim. Algebraicity of each `C_n(F)` is real quantifier
elimination on the first-order formula `for all U in U(n)^2: e(c) <= K max_i e(R_i)`.
- If `C = sup_n C_n(F) < infinity`, then `delta < epsilon/(C+1)` forces `||UW - WU||_2 < epsilon` in every dimension. That is
  statement 3 of `thompson-f-hyperlinear-iff-relator-system-hs-unstable`, which gives nonhyperlinearity.
- Conversely nonhyperlinearity gives statement 3, and at `epsilon = 1` a `delta` with `||c - I||_2 >= 1 => delta(U,W) >= delta`
  in every dimension. `fixed-hs-word-gap-is-linear-domination` with `eta = delta` gives `||c - I||_2 <= (2/delta) delta(U,W)`,
  so `sup_n C_n(F) <= 2/delta`.

**4. Degree escape.** Item 5 of the general claim with `|R| = 2`. Rearranging,
`4 (1 - mu_D) >= epsilon - 2 C_D(F)^2 delta^2 -> epsilon`.

**5. Lower bounds.**
- `W D W^-1` swaps the entries of a diagonal `D`, and `W^2 = -I`. So `c = U W U^-1 W^-1 = U^2`. For `A = W D_1` and
  `B = W D_2`, `[A,B] = (AB)^2 = D_1^-2 D_2^2`.
- With `x = UW^-1 = W(-U^-1)`, `y = U^-1 W U = W U^2` and `z = U^-2 W U^2 = W U^4`, this gives `R_1 = U^6` and `R_2 = U^10`.
- At `alpha = 3pi/8`, `e(c) = 2 - 2cos(3pi/4) = 2 + sqrt 2` and `e(R_1) = e(R_2) = 2 - 2cos(pi/4) = 2 - sqrt 2`. The ratio of
  square roots is `cot(pi/8) = 1 + sqrt 2`. `inspect_witnesses.py` checks this symbolically.
- The four-dimensional witness is stored as integer Cayley parameters in `ratio_search_n4.json`. `replay_verify.py` rebuilds
  `U, W` exactly over `Q(i)`, asserts exact unitarity, and checks `e(c) >= 3.2286^2 max_i e(R_i)` in exact rational arithmetic.
  Item 4 of the general claim extends the bound to all `n >= 4`.
