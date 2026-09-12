---
rg: 2
id: common-oriented-character-table-morita-proof
kind: route
title: Proof that a common oriented character table gives Morita-trace additivity
target: common-oriented-character-table-gives-morita-trace
requires: []
---

Let `(P_chi)_(chi in Omega)` be the PVM in the claim and put

```text
P_S=sum_(chi in S) P_chi
```

for `S subset Omega`.  Orthogonality of one common PVM gives, for disjoint
`S,T`,

```text
P_(S disjoint_union T)=P_S+P_T,
tr(P_(S disjoint_union T))=tr(P_S)+tr(P_T).            (1)
```

Apply (1) to `(OCT1)`.  This proves exactly

```text
mu(q+d)=mu(q)+mu(d),                                   (2)
```

which is `(MTA2)`.

For a named arrow from `a` to `d`, normalized trace is invariant under
unitary conjugacy and is dominated by normalized Hilbert--Schmidt distance
on contractions.  Thus `(OCT2)` gives

```text
|mu(a)-mu(d)|
 =|tr(W_(a,d) P_a W_(a,d)^*)-tr(P_d)|
 <=||W_(a,d) P_a W_(a,d)^*-P_d||_2
 <=eps.                                                (3)
```

This is `(MTA1)`.  Hypothesis `(OCT3)` is precisely `(MTA3)`.  All sets,
projections, and conjugator words belong to the fixed finite-depth menu, so
the same `eps=o(1)` is uniform in matrix dimension.  Consequently the three
Morita-trace axioms hold simultaneously on the prescribed seed carrier.

For completeness, if the PVM comes from an exact representation `sigma` of
a fixed finite abelian group `T`, then each table projection has the Fourier
formula

```text
P_chi=(1/|T|) sum_(t in T) conjugate(chi(t)) sigma(t). (4)
```

Hence a word `W` which approximately implements an automorphism `alpha` of
`T` transports every fixed subset projection with dimension-free error: if

```text
max_(t in T)||W sigma(t) W^*-sigma(alpha(t))||_2<=delta,
```

then, writing `alpha_* chi=chi composed alpha^(-1)`, (4) and the triangle
inequality give

```text
||W P_S W^*-P_(alpha_* S)||_2<=|S| delta.              (5)
```

Since `T` and the finite-depth menu are fixed, (5) is an admissible
dimension-independent contribution to `eps`.  The unresolved construction
problem is therefore not Fourier analysis; it is forcing one payload-coupled
orientation for which the subset identities and the prescribed-corner lower
bound hold in every microstate.

