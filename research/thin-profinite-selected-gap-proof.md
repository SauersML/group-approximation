---
rg: 2
id: thin-profinite-selected-gap-proof
kind: route
title: Transfer the finite-dimensional C-Laplacian gap through the selected weak-containment quotient
target: thin-profinite-selected-gap-lemma
requires: []
---

Set

```text
Delta_C=sum_i (1-c_i)^*(1-c_i) in C[A].                (1)
```

Hypothesis `(PSG1)` says that

```text
pi_FD^0(Delta_C) >= kappa I.                           (2)
```

Weak containment of `K_v` in `pi_FD^0` means that the representation on
`K_v` factors through the represented group C-star algebra of `pi_FD^0`.
The positive inequality `(2)` therefore passes to this quotient and gives

```text
kappa ||eta||_2^2
 <= <Ad pi(Delta_C)eta,eta>
 = sum_i ||Ad pi(c_i)eta-eta||_2^2.                    (3)
```

The projection `P_A` commutes with `Ad pi(A)`, and `P_Av` is `A`-fixed, so

```text
Ad pi(c_i)eta-eta=Ad pi(c_i)v-v.                       (4)
```

Tracial invariance identifies the last norm with
`||[v,pi(c_i)]-1||_2`, proving `(PSG3)`.  Finally,

```text
||[v,pi(a)]-1||_2
 =||Ad pi(a)eta-eta||_2
 <=2||eta||_2,                                         (5)
```

which together with `(PSG3)` proves `(PSG4)`.

For `C<A=SL_3(Z)`, every finite-dimensional representation of `A` has
finite congruence image.  Profinite co-density gives
`H_rho^C=H_rho^A`, while Bourgain--Varju supplies a uniform spectral gap on
their common orthogonal complement.  Hence `(PSG1)` is exactly the proved
finite-dimensional endpoint recorded in `sln-z-thin-codense-tau-pair`.
