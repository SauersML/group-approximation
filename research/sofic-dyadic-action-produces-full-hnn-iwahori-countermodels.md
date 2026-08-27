---
rg: 2
id: sofic-dyadic-action-produces-full-hnn-iwahori-countermodels
kind: claim
title: A sofic dyadic action produces positive-density Iwahori failures inside full canonical HNN microstates
distinct_from:
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that canonicalizes only the base amalgam character; this starts with canonical microstates of the entire centralizer HNN.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that uses an ordinary commuting lamp quotient; this retains all free stable-letter moments.
---

Assume the action

```text
A=SL_2(Z[1/2]) curvearrowright A/C,   C=SL_2(Z),
```

is sofic.  Put `G=<A,t | [t,C]=1>`.  Then there are canonical permutation
microstates of the **full group** `G` whose restrictions to the two modular
vertices may be perturbed by `o(1)` in normalized Hilbert--Schmidt norm to
exact same-dimensional representations `pi_(n,+),pi_(n,-)` such that:

```text
edge_defect(pi_(n,+),pi_(n,-)) -> 0,
max_(c in S_C)||[T_n,pi_(n,+)(c)]||_2 -> 0,
||[T_n,pi_(n,-)(a)]||_2 -> sqrt(2)                    (FHC1)
```

for every fixed `a in C_-\B_-` for which `[t,a] != 1`.  Moreover the graph
projections

```text
P_n=(1/2) [[1,T_n],[T_n^*,1]]                         (FHC2)
```

have trace exactly `1/2`, asymptotically commute with the doubled first
vertex, and have a second-vertex commutator bounded away from zero.  Hence
they are positive-density counterexamples to
`canonical-iwahori-projection-commutant-transfer`, now equipped with an
ambient full-HNN canonical microstate rather than only a regular base
character.

Proof.  By `sofic-dyadic-coset-action-makes-hnn-sofic`, `G` is sofic, so it
has canonical permutation microstates.  Same-dimension HS stability of
`PSL_2(Z)=C_2*C_3` corrects each vertex restriction to an exact
representation; the corrections are `o(1)`, so the edge defect, stable
letter commutators, and traces of fixed words are unchanged asymptotically.
The canonical trace of the nontrivial Britton word `[t,a]` gives the last
limit in `(FHC1)`.  Formula `(FHC2)` is an exact rank-half projection, and
direct block multiplication gives

```text
||[P_n,diag(U,U)]||_2=(1/2)||[T_n,U]||_2.             (FHC3)
```

This proves the assertion.
