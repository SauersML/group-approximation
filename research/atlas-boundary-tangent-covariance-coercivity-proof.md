---
rg: 2
id: atlas-boundary-tangent-covariance-coercivity-proof
kind: route
title: Fold-triviality telescopes every boundary derivative into differences of conjugations
target: atlas-boundary-tangent-covariance-coercivity
requires: []
artifacts:
  - experiments/atlas_asc_tangent_exact.py
  - experiments/atlas_asc_kernel_exact.py
  - experiments/asc-kernel-exact.json
  - experiments/asc-exact.json
  - research/artifacts/atlas-asc-tangent-exact-2026-08-19.md
---

## The telescope

Let `s = (f_1,g_1)...(f_L,g_L)` be a first-boundary word, transported through
the certified inner alignment.  Its total product is `1` in `A_8` -- this is
the property the classical fold has and the interior separator `c_19243`
does not, and it is what makes a quadratic form exist at all.  Write
`u_j = g_1...g_(j-1)` and `v_j = u_j g_j`.  Triviality forces the suffix,
`q_j = v_j^(-1)`, so for a K2 syllable

```text
lambda(u_j) [A, lambda(g_j)] lambda(q_j)
   = lambda(u_j) A lambda(u_j)^(-1) - lambda(v_j) A lambda(v_j)^(-1).
```

Every first-order term is a difference of **conjugations**.  With the
conjugation representation `rho(x)A = lambda(x)A lambda(x)^(-1)`,

```text
d/deps pi_s(exp(eps A))|_0 = rho(z_s) A,   z_s = sum_j (u_j - v_j) in Z[A_8].
```

The covariance side is the same kind of object, since
`||[A,lambda(h)]||_2 = ||rho(h^(-1))A - A||_2`.  Hence both forms are
`<A, rho(W) A>` for explicit positive self-adjoint elements

```text
W_pkt = sum_s z_s^* z_s        (support 101, trace 1516, coefficient sum 0),
W_cov = 4 - 2 h_a - 2 h_b      (support 3, trace 4, coefficient sum 0).
```

## The eigenvalue problem

`rho` and `lambda` are unitary representations of `A_8` containing every
irreducible constituent, and the generalized spectrum of a pair of group
algebra elements depends only on which irreducibles occur.  So the constant

```text
C_loc = max { lambda : rho(W_cov) x = lambda rho(W_pkt) x }
```

may be computed in the left regular representation: build the two
`20160 x 20160` group matrices `L[i,j] = W(m_i m_j^(-1))`, diagonalize the
positive one, check the kernel leak, and read the top eigenvalue of the
compression of the other to the support.  In double precision on one A100
the whole computation is 69 s, of which 33 s enumerates `GL(4,2)`.

## Numbers

```text
all 234 words   ker 120   leak 2.36e-17   C_loc = 0.07142857142857525
five words      ker 120   leak 2.18e-17   C_loc = 1.000000000000068
certified 24    ker 2358  leak 6.000000000009  -> first-order escape
```

`120 = 20160/168 = [A_8 : GL_3(2)]` is the dimension of the permutation
module on `A_8/H`, which is the `H`-fixed space summed over all irreducibles
with multiplicity -- an independent confirmation of the kernel identification
in `point15-boundary-tangent-equals-s3-covariance-kernel`, now for the whole
packet rather than the five-word screen.

## What would upgrade this from measured to certified

`C_loc <= C` is exactly positivity of the single element `C W_pkt - W_cov` of
`Q[A_8]` in every representation: 14 irreducibles of dimension at most 70, so
it is checkable in exact arithmetic, or by a sum-of-squares certificate
`C W_pkt - W_cov = sum_i y_i^* y_i` in `Q[A_8]`.  The tracial-SOS obstruction
recorded as item 6 of `atlas-two-s3-covariance-collapse` does not apply: that
rules out certificates valid in every finite tracial von Neumann algebra,
whereas this positivity lives in one finite group algebra.
