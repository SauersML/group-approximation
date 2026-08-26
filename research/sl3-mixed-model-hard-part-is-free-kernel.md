---
rg: 2
id: sl3-mixed-model-hard-part-is-free-kernel
kind: claim
title: The nonamenable sector of every mixed SL3 model must detect the whole free fold kernel
distinct_from:
  sl3-atomic-ambient-is-absorbed-by-lattice: that rules out an amenable exterior model of the arithmetic pair before forming an amalgam; this identifies exactly what an arbitrary mixed atomic--nonamenable model of the double or centralizer HNN must still represent faithfully.
  sl3-arithmetic-double-finite-representations-fold: that proves every finite-dimensional representation of the double kills its fold kernel; this computes that kernel as `F_infinity` and turns the observation into an exact positive-model equivalence after an arbitrary nonamenable sector is added.
  sl3-arithmetic-double-hyperlinear-iff-relative-embeddable: that characterizes hyperlinearity through Gao's relative embeddability of the canonical factor inclusion; this gives an abstract-unitary construction criterion requiring faithfulness only on one explicit free normal subgroup.
  exterior-hyperfinite-edge-model-amalgam-hyperlinear: that obtains injectivity by free amalgamation over an amenable subgroup algebra; this permits a nonamenable coefficient algebra, but proves that all hard injectivity is concentrated on the free fold kernel.
---

Put

```text
C=SL_3(Z),                 A=SL_3(Z[1/p]),
D=A *_C A,
H=<A,t | [t,C]=1>.
```

Let

```text
q_D:D->A
```

be the fold identifying the two vertex copies, and let

```text
q_H:H->A x Z
```

be the quotient which additionally makes `t` commute with all of `A`.  Then

```text
K_D=ker(q_D) ~= F_infinity,
K_H=ker(q_H) ~= F_infinity.                              (MFK1)
```

Every finite-dimensional unitary representation of `D` factors through
`q_D`, and every finite-dimensional unitary representation of `H` factors
through `q_H`.  Consequently every atomic direct-sum sector kills `K_D` or
`K_H` pointwise.

More precisely, for `G` equal to `D` or `H`, with the corresponding `q` and
`K`, the following are equivalent:

1. `G` is hyperlinear;
2. there are a Connes-embeddable finite tracial von Neumann algebra `M` and
   a homomorphism

   ```text
   psi:G->U(M)
   ```

   whose restriction to `K` is injective.                        `(MFK2)`

Indeed an arbitrary faithful atomic representation of the residually finite
quotient `q(G)` can be added to `psi`; the direct sum is faithful on `G`.
Conversely a hyperlinear embedding is faithful on every subgroup.

This is the smallest mixed-model positive surface left after atomic
absorption.  Atomic or profinite weight can separate the easy quotient and
nothing else.  If a proposed nonamenable Hecke-bimodule sector kills even
one nontrivial element of `K`, no amount of atomic padding repairs it.
Equivalently, a positive construction need not model the canonical trace or
be faithful on the quotient, but it must place one explicit normal
`F_infinity` faithfully inside a Connes-embeddable finite algebra while
implementing the ambient arithmetic conjugations.
