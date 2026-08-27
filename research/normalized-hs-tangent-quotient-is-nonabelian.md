---
rg: 2
id: normalized-hs-tangent-quotient-is-nonabelian
kind: claim
title: Sparse Pauli blocks keep the normalized-HS first-order tangent quotient nonabelian
distinct_from:
  hs-invisibility-inflation-no-go: that hides a fixed bad summand by padding an operator-norm approximation; this computes a first-order commutator that survives at exactly the normalized-HS tangent scale.
  commutant-density-trace-blind: that explains why one adjoint fixed direction has vanishing density; this gives an explicit pair of near-identity unitaries whose nonlinear interaction remains first order.
  tracial-coordinate-transport-barrier: that rules out transporting an individual almost-fixed operator through a tracial ultraproduct; this rules out the abelian tangent linearization used by submultiplicative-norm Ulam stability.
---

There are dimensions `d_n`, scales `epsilon_n->0`, and unitaries
`A_n,B_n in U(d_n)` such that

```text
||A_n-I||_2=sqrt(2)epsilon_n,
||B_n-I||_2=sqrt(2)epsilon_n,
||[A_n,B_n]-I||_2=2epsilon_n.                 (NHT1)
```

Consequently the normalized-HS first-order tangent quotient obtained by
modding `o(epsilon_n)` sequences out of `O(epsilon_n)` near-identity
sequences is not abelian. In particular, the defect-diminishing/asymptotic-
cohomology linearization used for Thompson groups with submultiplicative
matrix norms does not extend formally to normalized HS.

There is a sharp extra hypothesis under which the commutator does become
second order: if

```text
||A_n-I||_op=o(1),  ||B_n-I||_op=o(1),
||A_n-I||_2,||B_n-I||_2=O(epsilon_n),
```

then `||[A_n,B_n]-I||_2=o(epsilon_n)`. Thus an operator-diffuse/no-sparse-
outlier input would restore the tangent step, but normalized-HS microstates
do not supply it.
