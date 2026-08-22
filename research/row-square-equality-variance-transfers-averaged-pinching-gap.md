---
rg: 2
id: row-square-equality-variance-transfers-averaged-pinching-gap
kind: claim
title: Row-square equality variance transfers the averaged pinching gap
distinct_from:
  parity-exact-shared-contractions-have-intrinsic-cp-gap: that assumes literal sharing and warns that one occurrence replacement is operator-discontinuous; this averages all occurrence channels and uses a Loewner row-square hypothesis to recover dimension-free continuity.
  gapped-face-pinchings-give-same-hilbert-code-pvm-rounding: that starts from exact face PVMs and rounds generators against their common commutant; this transfers the Hamiltonian itself through unequal occurrence averaging.
  common-cut-contraction-sign-has-complete-balanced-energy-ledger: that controls fixed group-word energies under terminal sign; this controls the operator norm of the averaged adjoint channel on the whole Hilbert--Schmidt space.
---

ESTABLISHED AVERAGED EQUALITY TRANSFER.  Let occurrences `u` have positive
weights `w_u` summing to one and logical label `i(u)`.  Put

```text
 mu_i=sum_(u:i(u)=i)w_u,       lambda_(u|i)=w_u/mu_i,
 S_i=sum_(u:i(u)=i)lambda_(u|i)Q_u,                    (REV1)
```

where every `Q_u` is a reflection.  Thus `S_i` is the weighted shared
selfadjoint contraction.  Its conditional variance is exactly

```text
 V_i=sum_(u:i(u)=i)lambda_(u|i)(Q_u-S_i)^2=I-S_i^2.    (REV2)
```

Assume the common-cut row-square estimate

```text
 sum_i mu_i V_i<=epsilon I.                            (REV3)
```

Let `R_i=sgn(S_i)` and define the weighted occurrence and shared pinching
channels on Hilbert--Schmidt space by

```text
 C_Q(T)=sum_u w_u (T+Q_uTQ_u)/2,
 C_R(T)=sum_i mu_i (T+R_iTR_i)/2.                      (REV4)
```

Then, with no lower bound on any individual occurrence weight,

```text
 ||C_Q-C_R||_(L_2->L_2)<=sqrt(2epsilon).               (REV5)
```

Hence unequal occurrence multiplicities do not create a length loss once
the **weighted Loewner row square** is controlled.

Let `H_Q=I-C_Q` and `H_R=I-C_R`.  If `H_Q` has spectrum contained in
`{0} union [gamma,1]` and `kappa=sqrt(2epsilon)<gamma/2`, spectral
perturbation gives

```text
 spec(H_R) subset [0,kappa] union [gamma-kappa,1].      (REV6)
```

On the complement of the spectral projection
`1_[0,kappa](H_R)`, the current shared Green channel therefore has the
dimension-independent gap `gamma-kappa`; a fixed Green polynomial contracts
there by `(1-gamma+kappa)^K`.

The low band in `(REV6)` cannot in general be replaced by the exact shared
commutant.  Approximate equality may split an old zero eigenspace into small
positive eigenvalues, so a separate sparse-corner reset or low-band gauge is
still necessary.  The exponent in `(REV5)` is sharp: for two Pauli-axis
reflections meeting at angle `theta`, `(Q-R)^2=4sin^2(theta/2)I` while the
two pinching projections differ in `L_2` operator norm by `sin(theta)`, of
order the square root of the variance.
