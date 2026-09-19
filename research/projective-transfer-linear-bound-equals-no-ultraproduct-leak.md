---
rg: 2
id: projective-transfer-linear-bound-equals-no-ultraproduct-leak
kind: claim
title: A projective commutator transfer modulus exists exactly when tensor amplification finds no ultraproduct leak
distinct_from:
  projective-transfer-equals-rcc-for-perfect-pairs: that removes scalar phases in an already formed ultraproduct for perfect groups; this proves the missing uniform finite-level linear bound, including a linear presentation-defect term, by amplifying any failure of uniformity.
  balanced-replica-hs-amplification: that is the phase-balanced defect estimate for arbitrary unitary tables; this applies ordinary diagonal powers directly to projective commutator energies and proves a quantitative-versus-ultraproduct equivalence for one fixed presentation and subgroup packet.
  projective-trace-square-transfer-for-sl3-pair: that asserts the transfer for the arithmetic pair; this proves that its quantitative form is equivalent to excluding the corresponding leak in every matrix ultraproduct, but does not exclude that leak.
---

Fix a finite presentation `A=<X|R>`, words `S` in `X`, and a word `h`.
For an assignment `rho:X->U(d)` and `U in U(d)`, put

```text
delta(rho)=max_(r in R) ||rho(r)-I||_2,
q(rho,U)=sum_(s in S) (1-|tr([U,rho(s)])|^2),
e(rho,U)=1-|tr([U,rho(h)])|^2.                         (PL1)
```

The following are equivalent.

1. There is a finite constant `L` such that every assignment satisfies

   ```text
   e(rho,U) <= L(q(rho,U)+delta(rho)).                 (PL2)
   ```

2. There is no sequence `(rho_n,U_n)` with

   ```text
   delta(rho_n)->0,   q(rho_n,U_n)->0,
   liminf_n e(rho_n,U_n)>0.                            (PL3)
   ```

Thus an arbitrary modulus in a projective transfer statement costs nothing:
qualitative exclusion of a matrix-ultraproduct leak already gives a single
linear coefficient, even on the *unsquared* presentation defect.  Applied to
`SL_3(Z)<=SL_3(Z[1/2])`, the quantitative formulation of
`projective-trace-square-transfer-for-sl3-pair` is therefore exactly the
universal matrix-ultraproduct transfer problem, not an additional
Lojasiewicz or rate problem.

There is a consequential scope warning.  `(PL2)` quantifies over arbitrary
assignments and hence `(PL3)` over arbitrary matrix-ultraproduct
representations.  The HNN non-hyperlinearity route supplies only
regular-trace microstates.  Therefore the universal terminal claim is
strictly stronger in quantification than the regular-trace collapse actually
consumed by that route; tensor amplification removes the quantitative gap but
does not remove this trace-profile gap.
