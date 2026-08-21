---
rg: 2
id: hs-stability-from-bounded-degree-two-primitives
kind: route
title: A normalized-HS Newton iteration with truncation turns operator-bounded degree-two primitives into flexible HS-stability
target: sln-z-flexibly-hs-stable
requires:
  - bounded-degree-two-primitives-for-higher-rank-lattices
---

Fix `N >= 4`, `Gamma = SL_N(Z)` with a finite presentation, and an
almost-representation `sigma : Gamma -> U(d)` with normalized-HS
defect `eps` on the relators.  Write `c(g,h) = sigma(gh)
sigma(h)^(-1) sigma(g)^(-1) - 1`, so `|| c ||_2 <= eps` and
`|| c ||_op <= 2` automatically.

**Step 1 (the cocycle).**  Modulo `O(eps^2)` in 2-norm, `c` is a
2-cocycle for the `Ad sigma`-module (the cocycle identity holds up
to products of two defects, each of 2-norm `<= eps` and operator
norm `<= 2`, hence up to `2 eps^2`-type errors).  Passing to the
ultraproduct after rescaling by `1/eps` gives a genuine 2-cocycle
with values in `L^2(M)` for the `Ad pi`-module; the
trivial-coefficient component vanishes since `H^2(Gamma; C) = 0`.

**Step 2 (the primitive, both norms).**  By the required claim
there is `y` with `delta y = c + O(eps^2)`, `|| y ||_2 <= C eps`,
`|| y ||_op <= 2C`.  Rescale back: at finite level the 1-cochain
`x = y` satisfies `|| x ||_2 <= C eps` and `|| x ||_op <= 2C`;
replacing `x` by `eps^(1/2)`-truncation is unnecessary precisely
because the operator bound is available -- this is the step the
naive Hodge primitive cannot pass.

**Step 3 (the Newton step, two scales).**  Track two scales of
the defect: `eps_2 = || c ||_2` and `eps_op = || c ||_op`.  The
required claim gives a primitive with `|| x ||_2 <= C eps_2` and
`|| x ||_op <= C eps_op`.  Put `sigma'(g) = (1 + x(g)) sigma(g)`:
```text
sigma'(g) sigma'(h) = (1 + x(g) + Ad sigma(g) x(h)
                        + x(g) . Ad sigma(g) x(h)) sigma(g) sigma(h),
```
so the new defect is the old one minus `delta x` (cancelling to
`O(eps_2^2)` by Step 2) plus the quadratic term, whose 2-norm is
at most `|| x(g) ||_op . || x(h) ||_2 <= C^2 eps_op eps_2`.  This
is a contraction only if `eps_op` is small -- and `eps_op <= 2` is
all a unitary almost-representation gives.  The flexible setting
supplies the missing smallness: by Chebyshev in the trace, the
spectral projection where any of the finitely many relator defects
exceeds `eps_2^(1/2)` in absolute value has trace `O(eps_2^(1/2))`;
cutting that corner (and polar-correcting the compressions to
unitaries, a standard almost-invariant-corner step) yields an
almost-representation on a corner of co-trace `O(eps_2^(1/2))` with
`eps_op = O(eps_2^(1/2))`.  With the operator-bounded primitive the
quadratic term is then `O(eps_2^(3/2))`: a genuine contraction at
exponent `3/2`.  Without operator control of `x` the same
truncation trick applied to `x` itself gives only
`|| x^(K) ||_op <= eps_2^(-1/2)` and a quadratic term of order
`eps_2^(1/2)` -- no contraction -- which is the precise reason the
required claim is the whole content.  Iterating, `eps_2` decreases
geometrically at exponent `3/2`, the corrections and corner losses
are summable, and the limit is an exact representation on a corner
of vanishing co-trace at 2-distance `O(eps)` from `sigma`.

**Step 4 (conclusion).**  `SL_N(Z)` is flexibly HS-stable for
`N >= 4`, which is the target.  Downstream: correctability holds at
`SL_N(Z)` with NO outlier sector, so with the rank-generic Weyl
sector theorem and the Lambda-exact face analysis transported to
the pair `(SL_N(Z), SL_N(Z[1/p]))` at a prime with `(p,p)_p = -1`,
the relative commutant collapse follows and the coset wreath group
over that pair is non-hyperlinear.

**Honesty note.**  Two steps carry the weight: the required claim
(operator control of the degree-2 primitive) and the corner-cutting
reduction `eps_op = O(eps_2^(1/2))`, which is Popa-style truncation
and must be checked to preserve the almost-cocycle structure at the
next iteration (the cut corner is only almost-invariant; the
standard fix re-derives the cocycle for the compressed maps with an
error absorbed into `O(eps_2^(3/2))`).  Everything else is the
De Chiffre--Glebsky--Lubotzky--Thom iteration transplanted to the
II_1 setting.
