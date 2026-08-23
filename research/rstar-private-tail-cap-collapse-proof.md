---
rg: 2
id: rstar-private-tail-cap-collapse-proof
kind: route
title: Determinize each private tail over the retained binary spectrum
target: rstar-private-tail-fiberwise-cap-collapse
requires:
  - rstar-cap-support-is-one-character-row
---

Fix a context.  Its joint spectral projections `E_s` vanish off `R_*`, and

```text
P_a=sum_(s in R_*:s_1=a) E_s.                           (PTC6)
```

Thus an active `P_a` has an allowed tuple in its fibre.  Formula `(PTC4)` is
a self-adjoint involution because the active `P_a` are orthogonal and sum to
one.  All three new observables lie in `W^*(A_1)`, so they commute.  On the
`P_a` summand their joint value with `A_1` is exactly `r^a`; hence the whole
`R_*` predicate, including odd parity and ghost exclusion, remains satisfied.

The new support has at most one point above each of the two values of `x_1`.
After ghost translation its points are nonzero in `F_2^3`, and any subset of
at most two nonzero points is a Fano cap.  Apply
`rstar-cap-support-is-one-character-row` to obtain the character with value
`-I` in `(PTC5)`.  Concretely, one selected nonzero vector imposes one linear
condition `lambda(u)=1`; two distinct selected vectors are independent and
impose two consistent conditions.  Extend either prescription to a linear
functional.  This also shows why a common annihilator is the wrong
functional despite the validity of its homogeneous equation.

Occurrence-privacy makes the replacements independent across contexts.
Finally all new observables lie in the original CE algebra, and a
trace-preserving embedding into `R^omega` restricts to their generated von
Neumann subalgebra.
