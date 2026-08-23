---
rg: 2
id: sofic-coset-atlas-linearizes-to-exact-quasiregular-coboundary
kind: claim
title: A sofic coset atlas linearizes to an exact quasi-regular coboundary packet
artifacts:
  - research/artifacts/sl3-garland-coboundary-firewall-2026-08-23.md
distinct_from:
  global-schreier-pvm-is-stronger-than-action-soficity: that concerns a single globally indexed orthogonal PVM of positive trace; this extracts only the Hilbert-space packet canonically supplied by the moving GKEP charts, with no global PVM conclusion.
  sl3-double-tensor-leak-is-quasiregular: that extracts a quasi-regular tensor witness from canonical microstates of the arithmetic double; this works directly for every sofic coset-action atlas and identifies its displacement as an exact coboundary.
  sl3-lattice-inclusion-is-quasiregular-not-mixing: that is an intrinsic bimodule statement for the group-factor inclusion; this is a finite-atlas linearization theorem for GKEP action models.
---

Let `C<A` and suppose the transitive action `A action A/C` is sofic in the
Gao--Kunnawalkam Elayavalli--Patchell sense.  The permutation ultraproduct
associated to any witnessing sequence has a unitary representation
containing an isometric `A`-equivariant copy of

```text
l2(A/C).
```

In particular it contains a unit vector `xi_C` which is fixed by `C` and
whose translates satisfy

```text
<xi_(aC),xi_(bC)> = 1_(aC=bC).                            (SQA1)
```

The displacement

```text
b(a)=a xi_C-xi_C                                         (SQA2)
```

is therefore an **exact one-coboundary**, while

```text
b(c)=0  (c in C),       ||b(h)||=sqrt(2)  (h notin C).    (SQA3)
```

Consequently property `(T)`, Garland `H^1`-vanishing, and degree-one
coboundary expansion cannot by themselves upgrade the exact-finite-action
firewall to arbitrary approximate actions.  The packet already has zero
cohomology class.  On a two-dimensional building, its edge cochain is
`delta_0 xi_C`, hence has identically zero triangle curl
`delta_1 delta_0 xi_C`; a cofilling estimate modulo `im(delta_0)` is
saturated with zero left-hand side.

For `C=SL_3(Z)<A=SL_3(Z[1/2])`, the missing theorem must instead exclude
such a quasi-regular packet specifically inside **permutation
ultraproduct** representations of `A`, or prove relative invariant
transfer

```text
Fix_C(pi)=Fix_A(pi)                                      (SQA4)
```

on that restricted class.  Ordinary Garland expansion does not imply
`(SQA4)`: the genuine quasi-regular representation itself is an explicit
counterexample.

