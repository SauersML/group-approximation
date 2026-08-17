---
rg: 2
id: simple-kl-via-normal-rank-certificate
kind: route
title: Certify properness of the normal closure in a nonabelian quotient of the kernel
target: kl-holds-over-two-generator-simple-groups
requires: [uniform-normal-rank-certificate-for-degree-kernels, kl-simple-failure-leaves-only-the-cyclic-quotient]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Let `S` be two-generator nonabelian simple, `m >= 1`, and `w in N_m` with
`deg_t(w) = m`.  The first prerequisite supplies an action-compatible
quotient `q : N_m ->> D_w` in which `<<q(w)>>_{D_w}` is proper.  Normal
closure is preserved by a surjection compatible with the ambient
conjugation, so

    q( <<w>>_{S*<t>} )  =  <<q(w)>>  !=  D_w  =  q(N_m) ,

hence `<<w>>_{S*<t>} != N_m`.  As `w` was arbitrary of degree `m`, no
degree-`m` word normally generates `N_m`.

By part (a) of the second prerequisite, a failure of coefficient injectivity
over `S` would force exactly that normal generation.  So there is no failure,
which is the target.

## Where the work is

Entirely in the first prerequisite.  This route is the bookkeeping that turns
a proper-normal-closure certificate into a statement about equations, and it
is recorded separately so that the certificate can be attacked without
re-deriving the translation each time.  The translation is also what makes
the constraint from `degree-kernel-abelianization-is-infinite-cyclic` bite:
it says precisely which quotients `D_w` are useless.
