---
rg: 2
id: arithmetic-shift-conjugacy-period-proof
kind: route
title: Conjugate a source-period translation and take a common period of its image progressions
target: arithmetic-near-shift-actions-have-mixed-relations
requires:
  - a5-free-product-has-simple-arithmetic-shell-envelope
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

Set f=lambda*s^m*lambda^-1. For sufficiently large k,

    f(a_r*k+b_r)=a_r*(k+1)+b_r.

The finitely many image progressions partition a cofinite subset
of N: their disjointness follows from injectivity of lambda, and
their exhaustion from surjectivity. Hence on each progression f
is translation by a_r. If A is a multiple of every a_r, adding A
preserves each image progression sufficiently far out. Therefore
f(n+A)=f(n)+A on a tail, exactly the claimed near commutation.

In the free product P*<s>, for g!=1 and m,A>0, the word

    g*s^m*g^-1*s^A*g*s^-m*g^-1*s^-A

is a nonempty reduced word, since all P syllables and all displayed
shift powers are nonidentity and alternate. Its vanishing in the
actual near action proves the canonical map is not injective.

For the bijective-base A5 example, the required construction has
branch modulus 2*59=118 in the single-ray index n and slopes
59, 1, and 1/59. In coordinates n=118*k+r the corresponding
coefficients a_r are 6962, 118, and 2. Their least common multiple
is 6962. The finitely many empty-word and one-syllable exceptions
do not change the near relation. These are the single-ray maps
lambda, not the doubled even-shell maps rho; no parity factor
is omitted in the stated constants.
