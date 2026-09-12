---
rg: 2
id: leavitt-rho5-split-multiplicities-are-feasible
kind: claim
title: Every exact frozen Leavitt S3 anchor admits the multiplicities of the rho5 split
distinct_from:
  frozen-cycle-extracts-a-coarse-prefix-pvm: That supplies a covariant coarse PVM and obstructs its fine B transports; this tests the three commuting involutions in the rho5 split and proves their finite-dimensional multiplicities are always feasible for the authenticated anchor.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: That realizes arbitrary depth contextual clone data; this gives the necessary and sufficient single-split rank criterion and checks it against the actual native root determinant and frozen cycle profile.
artifacts:
  - research/artifacts/leavitt-rho5-split-multiplicity-is-not-an-obstruction-2026-09-08.md
---

Let `A,D` be self-adjoint unitaries in dimension `n`, each with negative
eigenspace dimension `q`. There exist commuting self-adjoint unitaries
`U,V`, each unitarily conjugate to `A`, with `UV=D`, if and only if

```text
q is even,       3q<=2n.
```

Their three nontrivial joint sign spaces necessarily each have
dimension `q/2`, and the remaining space has dimension `n-3q/2`.

For the actual Leavitt source words, suppose the frozen cycle `C`
has dimension `n=3m=24k` and the exact anchor relations
`A^2=(AC)^2=I` hold, with `A=j` and `D=C^(-1)AC`. Then
`q=m+b` for some integer `0<=b<=m`, and `q` is even because
`det A=det d=1` for the derived commutator `d`. Thus every such
anchor satisfies the criterion.

The actual row `rho_5` specifies `U=A^(E_0)` and `V=A^(E_1)` for
two fixed words involving `A,B,D`. The existence above supplies no
equality with those prescribed occurrences. It proves that a test
retaining only the split equation and the conjugacy spectra cannot
give an additional rank obstruction. No exact full-packet model or
dimension-uniform gap is asserted.
