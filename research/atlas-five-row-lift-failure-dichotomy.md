---
rg: 2
id: atlas-five-row-lift-failure-dichotomy
kind: claim
title: Failure of the five-row lift is either a macroscopic ultraproduct escape or a normalized blow-up escape
distinct_from:
  atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test: that classifies exact finite-dimensional zero-defect escapes by finite quotients; this proves that such exact zeros detect only the macroscopic branch and isolates a second vanishing-signal branch.
  atlas-six-relator-leavitt-tracial-countermodel: that supplies a macroscopic exact escape in the canonical Leavitt trace; this is a compactness dichotomy for finite regular-multiplicity sequences.
  atlas-aligned-quotient-spectrum-cannot-reach-low-defect: that rules out using the aligned local Hessian on low-defect frames; this identifies the normalized blow-up object which remains after exact-zero screening.
---

For `U in U(20160k)` put

```text
A_k(U)=sum_(j in {0,11,30,44,55}) ||rho(z_j)U||_2^2,
B_k(U)=sum_(j in {0,11,30,44,55}) ||pi_U(s_j)-1||_2^2
       +||pi_U(c_19243)-1||_2^2.                       (FPG1)
```

Then `atlas-five-row-operator-phase-lift` is equivalent to

```text
inf_(k,U:A_k(U)>0) B_k(U)/A_k(U)>0.                    (FPG2)
```

If `(FPG2)` fails, after passing to a subsequence exactly one of the
following two alternatives occurs.

1. **Macroscopic escape.**  There are `k_n,U_n` and `a>0` with

   ```text
   B_(k_n)(U_n)->0,       A_(k_n)(U_n)->a.             (FPG3)
   ```

   Hence the `U_n` define in a tracial matrix ultraproduct an exact common-
   orbit solution of the six nonlinear phase relations with positive
   five-row additive energy.

2. **Normalized blow-up escape.**  There are `k_n,U_n` with

   ```text
   eta_n=sqrt(A_(k_n)(U_n))->0,
   B_(k_n)(U_n)/eta_n^2->0.                            (FPG4)
   ```

   In the Hilbert ultraproduct of the five row spaces, the vectors

   ```text
   Xi_n=(rho(z_j)U_n/eta_n)_j                         (FPG5)
   ```

   have norm one, whereas every one of the six nonlinear residuals divided
   by `eta_n` tends to zero:

   ```text
   ||pi_(U_n)(s_j)-1||_2/eta_n ->0,
   ||pi_(U_n)(c_19243)-1||_2/eta_n ->0.                (FPG6)
   ```

In particular, excluding finite-dimensional exact zeros--even in every
fixed multiplicity--does not reduce the five-row lift to a finite exact
linear-algebra calculation.  It removes only alternative 1 when the exact
ultraproduct escape lifts to a finite quotient.  A proof must additionally
exclude the dimension-moving blow-up cone `(FPG4)--(FPG6)` with a uniform
estimate.

## Proof

The equivalence `(FPG2)` is just the definition of the best constant in

```text
A_k(U)<=C_5 B_k(U).
```

If it fails, choose `k_n,U_n` with `A_(k_n)(U_n)>0` and

```text
B_(k_n)(U_n)/A_(k_n)(U_n)->0.                          (FPG7)
```

The five integral rows are fixed finite sums of unitaries, so `A_k(U)` is
bounded above independently of `k` and `U`.  Pass to a subsequence on which
`A_(k_n)(U_n)` converges to some `a>=0`.

If `a>0`, `(FPG7)` gives `(FPG3)`.  Word evaluation and the row quadratic
forms pass to a tracial matrix ultraproduct, giving the asserted exact
positive-energy model.

If `a=0`, set `eta_n=sqrt(A_(k_n)(U_n))`.  Equation `(FPG5)` has squared
Hilbert norm exactly one.  Since every summand of `B` is nonnegative,
`(FPG7)` implies each assertion in `(FPG6)`, proving the second alternative.
The two alternatives are disjoint because their additive energies converge
respectively to a positive number and to zero.  This proves the dichotomy.

## Certificate audit

The finite-quotient equivalence
`atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test` is therefore
an exact test only for finite-dimensional instances of the macroscopic
branch.  It cannot certify `(FPG2)` by itself.  Conversely, the favorable
finite irrep-pair spectrum at an aligned frame does not certify the blow-up
branch: `atlas-aligned-quotient-spectrum-cannot-reach-low-defect` proves that
every low-six-relator-defect sequence stays at least `sqrt(2)/16` from the
entire aligned commutant manifold.  The remaining certificate would have to
be a global, multiplicity-uniform exclusion of `(FPG4)--(FPG6)` on that
remote branch.  That exclusion is already the quantitative content of the
open five-row lift, not a bounded exact-zero computation.
