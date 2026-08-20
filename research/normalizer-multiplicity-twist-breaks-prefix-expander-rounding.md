---
rg: 2
id: normalizer-multiplicity-twist-breaks-prefix-expander-rounding
kind: claim
title: A Clifford normalizer can hide its expander in the external multiplicity factor
invalidates:
  - toeplitz-expander-rounds-relative-clifford-cell
distinct_from:
  quantum-expander-relative-commutant-rounding: that theorem correctly assumes the checks are `U_j tensor I`; this shows ordinary normalizer relations do not supply that assumption.
  pauli-generator-average-has-inverse-linear-gap: coordinate Pauli generators act trivially on multiplicity by definition, so the counterexample does not affect the polynomial Pauli-channel repair.
---

Let `N` be a finite Heisenberg/Pauli group with irreducible negative-central-
character representation `sigma` on `H`, and let a finite quotient `Q` act on
`N`.  Choose projective Clifford implementers `C_q` on `H`.  There is an
honest representation of `N semidirect Q` on `H tensor conjugate(H)` given by

```text
n |-> sigma(n) tensor I,
q |-> C_q tensor conjugate(C_q).                               (NMT1)
```

The two projective cocycles cancel.  The vector

```text
Omega=sum_i e_i tensor conjugate(e_i)
```

is fixed by every operator in the second line of `(NMT1)`.  Hence the
involution `Y=2|Omega><Omega|/||Omega||^2-I` commutes with every chosen
Clifford-normalizer check.  But `Y` is not in the commutant of
`sigma(N) tensor I`.

Therefore, even if the `C_q` form a perfect constant-gap quantum expander on
one irreducible spin block, the corresponding group words in an arbitrary
representation need only have the form `C_q tensor W_q`, not
`C_q tensor I`.  Their commutant can contain correlated spin--multiplicity
operators.  Embedding the finite Jacobi tables into a Toeplitz head does not,
by itself, justify the hypothesis of
`quantum-expander-relative-commutant-rounding`.

This invalidates the stated Toeplitz proof of the depth-independent relative
cell theorem.  The polynomial coordinate-Pauli proof is unaffected and is
the correct replacement for the contraction ledger.

