---
rg: 2
id: affine-finitary-linear-radical-is-the-whole-kernel
kind: claim
title: Over the integral affine base the finitary linear MF radical and compression defect are both the whole simple kernel
distinct_from:
  affine-perfect-lamp-wreath-has-locally-finite-mf-radical: that computes the radical of an ordinary A_5-lamp wreath over the level-three congruence base, and its radical is a restricted direct sum, locally finite but far from simple; this is the finitary linear extension over the full integral affine base, its radical is simple, and its proof consumes only the finite-central Kazhdan criterion.
  dyadic-perturbation-group-mf-radical-is-finitary-alternating: that computes the radical of one concrete finitary PERMUTATION group and gets the finitary alternating group by a different theorem, because the Kazhdan criterion is inert there; this is the finitary linear extension over the same family of bases, where the criterion does fire and the radical is the entire kernel.
  ascending-hnn-finitary-linear-family-is-sofic-non-mf: that is the general family over an arbitrary admissible self-embedding, where the radical identity is conditional on residual finiteness of the faithful quotient; this is the arithmetic instance in which that quotient is the base itself and is residually finite, so both subgroups are computed outright.
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

**ESTABLISHED.** Take `L = Z^3 x| SL_3(Z)`, whose property (T) is
`affine-semidirect-sl3-source-has-property-t`, and
`alpha(b,A) = (mb, A)` for any `m >= 2`, injective of index `m^3`.
Then

```text
V = Z[1/m]^3 x| (SL_3(Z) x Z),    X = V/L,
G = GL_fin(F_2^(X)) x| V,
```

and

```text
D_G(L) = Rad_MF(G) = GL_fin(F_2^(X)),     G/Rad_MF(G) ~= V.
```

`G` is finitely generated, sofic, not MF, and has no nontrivial finite
normal subgroup. Its MF radical is an infinite, locally finite, **simple**
group, and it is exactly the intrinsic compression-centralizer defect.

The kernel of the coset action is trivial, so the faithful quotient is
`V` itself: an affine map fixing every `v + m^j Z^3` has scale zero,
and then `(A-I)v + b` lies in the intersection of the `m^j Z^3`,
which is zero, for every `v`, forcing `A = I` and `b = 0`.
Residual finiteness of `V` is reduction modulo primes not dividing
`m`, on the faithful affine model `[[m^k A, b],[0,1]]`, whose
upper-left determinant recovers `k`.

The same argument runs over `Z^d x| SL_d(Z)` for every `d >= 3`, but
only the rank-three property-(T) input is established in this archive, so
only that rank is claimed here.

DERIVATION
affine-finitary-linear-radical-proof
