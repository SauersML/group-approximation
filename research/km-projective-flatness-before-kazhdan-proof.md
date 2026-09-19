---
rg: 2
id: km-projective-flatness-before-kazhdan-proof
kind: route
title: Descend the adjoint action, apply the Kazhdan gap, and polar-round in the commutant
target: km-kazhdan-holonomy-rounding-starts-after-projective-flatness
requires:
  - kazhdan-projection-rounding
  - simple-kazhdan-kac-moody-lattices-exist
---

The kernel of the adjoint representation of `U(D)` consists exactly of the
scalar unitaries. Therefore `Ad rho` kills the normal closure of `R` if and
only if every defining relator has scalar image, proving the equivalence
between `(KKH1)` factoring through `Gamma` and `(KKH2)`.

Assume `(KKH2)`. Apply the Kazhdan inequality to the exact representation
`Ad rho` on `L^2(M_D)`. Its invariant space is

```text
L^2(N),                  N=rho(F)' cap M_D.
```

Writing `E_N` for the trace-preserving conditional expectation gives

```text
delta=||W-E_N(W)||_2
 <=kappa^(-1) max_(s in S)||[W,rho(s)]||_2.            (KPF1)
```

Put `a=E_N(W)`. Extend the polar part of `a` to a unitary `V in N`. Since
conditional expectation is the `L^2` orthogonal projection and `W` is
unitary,

```text
1=||a||_2^2+delta^2,
||a-V||_2^2=tau((1-|a|)^2)
            <=tau(1-|a|^2)=delta^2.                  (KPF2)
```

The two differences `W-a` and `a-V` are orthogonal, so

```text
||W-V||_2^2<=2delta^2.                                (KPF3)
```

Combining `(KPF1)` and `(KPF3)` proves `(KKH3)`.

For the simple Kac--Moody lattice, `(KKH2)` defines a homomorphism
`Gamma->PU(D)`. If it were nontrivial, simplicity would make it injective.
Its finitely generated linear image would be residually finite by Malcev,
forcing the infinite simple group `Gamma` to be residually finite, which is
impossible. Thus the projective homomorphism is trivial and all generator
images are scalar. A scalar representation of a nontrivial finite parahoric
cannot contain its regular representation, proving the regular-core
collapse.

In the triangle presentation, `rho` is supplied exactly on the tree-first
amalgam. The free kernel basis gives the remaining defining relators.
Requiring their images to be scalar is therefore exactly the condition that
the tree-side adjoint local system descend through the missing `P_13` face.
With only small kernel defects there is no exact `Gamma`-representation on
which to invoke the Kazhdan inequality; assuming one would beg the relative
three-chart correction problem.
---
