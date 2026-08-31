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
  - experiments/verify_atlas_asc_one_fourteenth.py
  - experiments/atlas-asc-one-fourteenth-exact.json
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

## Exact finite-group certificate

The desired constant is equivalent to positivity of

```text
W_pkt - 14 W_cov
```

in every representation of `A_8`.  The verifier
`experiments/verify_atlas_asc_one_fourteenth.py` checks this without floating
point.  It reconstructs the 234 literal boundary words, obtains `W_pkt` with
support `101`, identity coefficient `1516`, and coefficient sum `0`, and
rebuilds the exceptional isomorphism `GL(4,2) ~= A_8` on all `20160`
elements.

The irreducible check uses one partition in every conjugate pair of
partitions of `8`.  Restriction from `S_8` to `A_8` identifies conjugate
non-self-conjugate Specht modules, while a self-conjugate Specht module
splits into the two corresponding `A_8` irreducibles.  Thus the twelve
selected rational Young-seminormal sectors cover all fourteen irreducible
`A_8` representations; positivity on a full self-conjugate restriction
checks both summands.

For each sector the verifier checks the Coxeter relations exactly, constructs
a positive rational diagonal Gram form `G`, verifies that
`G sigma(W_pkt-14 W_cov)` is symmetric, and performs exact rational symmetric
elimination.  Positive pivots are removed by Schur complement; when no
positive diagonal remains, the residual matrix is required to be exactly
zero.  Hence every sector is positive semidefinite.  The coefficient hash is

```text
b2cb3ba7e9abb8e7d23f43670707420b94b489f070977a27aedaa00d0ed7c3f5.
```

The exact kernels carry nonzero `W_cov` in the `[6,2]`, `[5,1,1,1]`, and
`[4,4]` sectors, so equality is attained with positive covariance and the
constant `1/14` is sharp.  The machine-readable sector summary is
`experiments/atlas-asc-one-fourteenth-exact.json`.

The earlier regular-representation computation remains an independent
numerical cross-check:

```text
all 234 words   ker 120   leak 2.36e-17   C_loc = 0.07142857142857525
five words      ker 120   leak 2.18e-17   C_loc = 1.000000000000068
certified 24    ker 2358  leak 6.000000000009  -> first-order escape
```

Here `120 = 20160/168 = [A_8 : GL_3(2)]` is the dimension of the permutation
module on `A_8/H`, agreeing independently with the exact kernel
identification.  The finite-group certificate does not address the remaining
analytic comparison between linear energy and the full nonlinear packet
defect.
