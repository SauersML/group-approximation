---
rg: 2
id: vanishing-codimension-compressions-obey-projective-transfer
kind: claim
title: Vanishing-codimension polar compressions cannot be SL3 projective-transfer enemies
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that treats exact finite-dimensional ambient representations; this permits the standard noncorrectable same-dimension polar compressions of those representations.
  sl3-projective-transfer-enemy-dichotomy: that leaves every uniformly noncorrectable inner-adjoint sequence as one branch; this removes the canonical large-irrep deletion construction from that branch.
  direct-sum-weil-compressions-have-quadratic-padding: that tracks a specific fixed-line Weil compression and its padding density; this applies to arbitrary exact SL3 representations and arbitrary subspaces of vanishing relative codimension.
---

Let

```text
C=SL_3(Z) < A=SL_3(Z[1/2])=<C,h>.
```

For every `n`, let `pi_n:A->U(H_n)` be an exact finite-dimensional
representation and let `P_n` be a projection of rank `m_n` with

```text
r_n=dim(H_n)-m_n,             r_n/dim(H_n) -> 0.       (VCP1)
```

For each fixed presentation generator `g`, let `rho_n(g)` be any unitary
polar correction of the compression `P_n pi_n(g) P_n` on `P_n H_n`.  Then
for every `U_n in U(P_n H_n)`, if

```text
sum_(c in S_C) (1-|tr([U_n,rho_n(c)])|^2) -> 0,        (VCP2)
```

one has

```text
1-|tr([U_n,rho_n(h)])|^2 -> 0.                         (VCP3)
```

More quantitatively, for one constant `K` depending only on the fixed words,
the Kazhdan constant, and the presentation,

```text
E_h(rho_n,U_n)
 <= K ( sum_(c in S_C) E_c(rho_n,U_n) + r_n/dim(H_n) ). (VCP4)
```

Changing `dim(H_n)` to `m_n` in the final error only changes the constant
once `r_n/dim(H_n)<=1/2`.

This includes the universal normalized-HS instability construction for
finitely generated residually finite non-virtually-abelian groups: compress
an irreducible representation of dimension `d` to dimension `d-1` and polar
correct.  Those almost representations may stay far from every exact
same-dimensional representation, but they cannot carry a projectively
`C`-central witness which leaks at `h`.  Thus ordinary uniform HS instability
of `SL_3(Z)` or `SL_3(Z[1/2])` is not a counterexample to the projective
transfer terminal.

The result does not address compressions deleting a positive density, nor
approximate representations which are not polar compressions of exact
representations.  Those remain in the two enemy branches already recorded in
Cairn.
