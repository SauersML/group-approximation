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
`vL(Lambda)v^*`.

For an arbitrary `beta`-cocycle, the Fourier coefficient calculation gives

```text
tau_M(c_g u_g)=0                    (g!=e).             (CFG3)
```

The map `g |-> c_g u_g` is a homomorphism by the cocycle identity, and
`(CFG3)` says its trace is the canonical group trace.  Its generated von
Neumann algebra `N_c` is therefore trace-preservingly isomorphic to
`L(Lambda)`.

There is a stronger internal obstruction.  The unitaries

```text
v_g=c_g u_g
```

are an orthonormal group basis of `L^2(N_c)`.  Hence every `x in N_c` has,
inside `L^2(M)`, a Fourier expansion

```text
x=sum_g a_g c_g u_g,                 a_g in C.         (CFG4)
```

If `x` also lies in `A`, crossed-product Fourier uniqueness makes every
nonidentity coefficient zero.  Since each `c_g` is unitary, `(CFG4)` forces
`a_g=0` for `g!=e`; normalization gives `c_e=1`, so `x=a_e1`.  Therefore

```text
N_c intersection A=C1.                                (CFG5)
```

In particular no coordinate copy of `Q` is contained in `N_c`.  A corner
or abstract normal quotient retaining an isomorphic copy of `Q` would have
to be produced by additional structure internal to `L(Lambda)`;
coinduction and its cocycles supply no such structure.
