---
rg: 2
id: coinduced-factor-generation-firewall-proof
kind: route
title: Separate the coinduced tensor coordinates from the canonical group unitaries
target: probability-coinduction-retains-factor-but-not-group-generation
requires:
  - coinduction-preserves-but-cannot-create-algebraic-envelope
  - cdi-character-rigid-image-quotient-is-an-exact-bridge
---

The product trace makes `(PCF1)` finite, and the coinduced action preserves
it.  Its restriction to any one tensor coordinate is the original trace on
`Q`.  Connes embeddability passes to von Neumann subalgebras, so embeddability
of `A` would imply embeddability of `Q`; likewise `A` is a subalgebra of the
finite crossed product `M`.  This proves the nonembeddability assertions.

The canonical unitaries satisfy the untwisted group multiplication table
and

```text
tau_M(u_g)=delta_(g,e).                                (CFG1)
```

Therefore their generated von Neumann algebra is trace-preservingly
isomorphic to `L(Lambda)`.  Fourier uniqueness in the crossed product gives
the intersection statement: if an element lies both in `A` and in the weak
closure of the scalar Fourier sums `sum_g a_g u_g`, all nonidentity Fourier
coefficients vanish and its identity coefficient is scalar.  Hence it lies
in `C1`, proving `(PCF3)`.

If `c_g=v beta_g(v^*)` is a coboundary, then

```text
c_g u_g=v u_g v^*,                                    (CFG2)
```

so the representation in `(PCF4)` generates only the conjugate
`vL(Lambda)v^*`.  A successful cocycle must therefore be genuinely
nontrivial and must also satisfy the much stronger generation/recoverability
condition.  Standard coinduction supplies the action but neither property.
