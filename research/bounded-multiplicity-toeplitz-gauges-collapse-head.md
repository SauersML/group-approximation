---
rg: 2
id: bounded-multiplicity-toeplitz-gauges-collapse-head
kind: claim
title: Bounded multiplicity forces commutant-gauged Toeplitz heads to collapse
distinct_from:
  bounded-block-jacobson-microstates-also-collapse: that bounds the irreducible degrees of the whole tuple; this permits unbounded carrier degrees and bounds only the commutant multiplicities.
  scalar-rephased-toeplitz-sections-still-collapse-head: that permits scalar phases; this permits noncommuting unitary gauges in bounded-dimensional multiplicity spaces.
  unbounded-commutant-coherence-is-the-original-gate: that removes the multiplicity bound and recovers the original microstate problem; this proves collapse under that bound.
---

Use the fixed Tietze-expanded Jacobson presentation and its marked head
word `w` from `toeplitz-folner-compressions-cannot-retain-jacobson-head`.
For the truncated-shift substitution
`theta_N:Sigma->F_N=GL_(28N)(F_2)`, let `rho:F_N->U(H)` be any
finite-dimensional representation. Choose arbitrary unitaries
`Z_s in rho(F_N)'` and set `U_s=rho(theta_N(s))Z_s`.
The gauges need not commute with one another.

If every irreducible type of `rho` occurs with multiplicity at most a
fixed `K`, there is a modulus `Omega_K(t)->0` as `t->0` such that

```text
||w(U)-I||_2 <= Omega_K(delta(U)),
delta(U)=max_(r in R)||r(U)-I||_2.                       (BCT1)
```

The modulus is independent of `N`, the representation dimension, and
the dimensions and number of its irreducible types. More precisely the
proof gives constants `A_0,A_1` depending only on the presentation and
the bounded-block modulus `omega_K` such that

```text
Omega_K(t)=2 A_0 t+omega_K(A_1 t).
```

The same argument, before using the multiplicity bound, gives

```text
||rho(theta_N(w))-I||_2 <= 2 A_0 delta(U),
delta(Z) <= A_1 delta(U).
```

Thus the bound closes the commutant ansatz with bounded multiplicities.
It does not apply to unbounded multiplicities or to perturbations outside
the carrier commutant. This statement is extracted from the surviving
current proof below; it is not a claim of general Jacobson HS stability.

DERIVATION
commutator-character-gap-and-endpoint-filling-proof
