---
rg: 2
id: atlas-boundary-tangent-covariance-coercivity
kind: claim
title: The full first-boundary packet controls both raw S3 covariances at first order, with dimension-free constant one fourteenth
distinct_from:
  atlas-two-s3-covariance-collapse: that is the global dimension-free implication for arbitrary chart unitaries and arbitrary multiplicity; this is the exact FIRST-ORDER inequality at the certified classical fold, with a rational constant that is independent of the multiplicity. The global claim stays open, and the exact characteristic-two countermodel recorded there is untouched by any local statement.
  atlas-flip-first-order-rigidity: that says the first derivative of every relator defect VANISHES at the tensor flip of the rank-five criterion; this is a second-order coercivity comparison between two nonvanishing quadratic forms at the classical fold of the regular-A8 criterion, and neither is a special case of the other.
  point15-boundary-tangent-equals-s3-covariance-kernel: that identifies the derivative kernel of the five-word tangent screen with the S3 covariance kernel qualitatively; this computes the kernel for the entire 234-word boundary packet and the sharp constant relating the two energies.
artifacts:
  - research/artifacts/atlas-asc-tangent-exact-2026-08-19.md
  - experiments/atlas_asc_tangent_exact.py
  - experiments/atlas_asc_packet_build.py
  - experiments/atlas_asc_covariance_gpu.py
---

ESTABLISHED by exact reduction to one integral group algebra, then one
generalized eigenvalue problem.

Work in the canonical regular-`A_8` criterion of
`leavitt-regular-atlas-hyperlinearity-criterion` at multiplicity `k = 1`,
at the certified classical fold `U = I`, where every one of the 234
first-boundary words is exactly trivial.  For `U = exp(eps A)` with `A`
skew-Hermitian put

```text
D(A)    = sum_(s in boundary) || d/deps pi_s ||_2^2,
Ncov(A) = ||[A,lambda(h_a)]||_2^2 + ||[A,lambda(h_b)]||_2^2,
```

with `h_a,h_b` the two raw `S_3` involutions of `TRUE_RAW_WORD_REYNOLDS_GAP`.
Then:

1. **The derivative kernel is the `H`-fixed space, for the whole packet.**
   `dim ker D = 120 = [A_8 : H]` with `H = GL_3(2)`, and the same kernel is
   already cut out by the five words `0, 11, 30, 44, 55` alone.  No further
   boundary word adds first-order information: the boundary packet is
   first-order saturated at five words.

2. **`Ncov` vanishes on that kernel** (measured `2.4e-17` in double
   precision), so no first-order escape exists for the boundary packet.

3. **Sharp constants.**

```text
Ncov(A) <= (1/14) * D(A)                                (all 234 words)
Ncov(A) <=   1    * D_{0,11,30,44,55}(A)                (the five tangent words)
```

   both attained, the first as `0.07142857142857525` and the second as
   `1.000000000000068`.

4. **The constant is dimension-free.**  At multiplicity `k` the tangent
   forms are `<A, rho_k(W) A>` for the SAME two elements `W` of `Z[A_8]`,
   with `rho_k(x)A = (lambda(x) (x) I_k) A (lambda(x) (x) I_k)^(-1)`.  The
   conjugation module `M_(20160k)` contains every irreducible constituent of
   `A_8` for every `k >= 1`, and the generalized spectrum of a pair of group
   algebra elements depends only on which irreducibles occur, so `C_loc` is
   `1/14` at every multiplicity.  This is the uniformity `(ASCq)` asks for --
   at first order.

Against the proved floor `a^2+b^2 >= 1/40` of
`raw-swap-forces-two-s3-covariance-energy`, (3) says that a microstate
sitting in a neighbourhood of the classical fold must carry total boundary
energy at least `14/40 = 0.35`, hence
`max_s ||pi_U(s)-1||_2 >= sqrt(0.35/234) = 0.0387`.

The statement is local; the open claim
`atlas-two-s3-covariance-collapse` is neither implied nor contradicted by it.
What it supplies is exactly the local-coercivity input that item 5 of that
node asks the tangent gap to provide.
