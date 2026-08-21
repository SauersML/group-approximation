---
rg: 2
id: twisted-group-basis-forces-affine-context-support
kind: claim
title: Native twisted-group basis observables force every Boolean context onto one uniform affine slice
distinct_from:
  central-pinning-forbids-nonlinear-predicates: that derives affine support from a finite packet with a unique central-sign irreducible; this requires neither finiteness nor sector uniqueness and applies to arbitrary canonical projective bases of twisted group factors.
  projective-basis-character-criterion: that decides when a whole GNS factor has a projective group basis; this computes the joint law of commuting involutions already chosen from such a basis.
---

Let `(M,tau)=L_omega(Gamma)` have canonical projective orthonormal basis
`{u_g}`. If commuting self-adjoint involutions

```text
x_i=zeta_i u_(g_i),       i=1,...,k,
```

are native basis elements, then their joint spectral distribution is uniform
on one affine subspace of `F_2^k` and zero elsewhere.

More precisely, for `s in F_2^k` put `X(s)=product_i x_i^(s_i)`. The map
`X` is an honest homomorphism. Let `K` be the kernel of its map to basis
indices, equivalently the set on which `X(s)` is scalar, and write
`X(s)=(-1)^(a_0 dot s)I` on `K`. For the joint atom `p_a`,

```text
tau(p_a)=|K|/2^k  if a in a_0+K^perp,
tau(p_a)=0        otherwise.
```

Faithfulness makes this affine coset the exact joint spectrum. Therefore a BCS
context with allowed relation `R` is satisfied by native basis observables
exactly when its affine support is contained in `R`. Every such model factors
through the affine/LCS refinement obtained by replacing each nonlinear context
with its occupied affine slice. A genuinely nonlinear native support is
impossible; using Fourier sums of basis elements returns to the additive-corner
groupification bottleneck.
