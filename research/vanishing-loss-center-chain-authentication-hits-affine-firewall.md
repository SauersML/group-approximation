---
rg: 2
id: vanishing-loss-center-chain-authentication-hits-affine-firewall
kind: claim
title: Vanishing-loss center-chain authentication converges to the forbidden fixed regular corner
artifacts:
  - research/vanishing-loss-center-chain-firewall-proof.md
distinct_from:
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that rules out an exact fixed ordinary-word occurrence row; this proves that representation-dependent subprojections discarding vanishing ambient trace converge to the same fixed corner and hence cannot evade that obstruction.
  center-chain-common-source-authenticates-native-covariances: that is the positive finite-matrix authentication leaf; this gives the quantitative contradiction which follows if such authentication is achieved with vanishing loss.
---

**ESTABLISHED VANISHING-LOSS FIREWALL.**  Retain the fixed projections
`Q,P` and common-source Hecke partial isometries

```text
S_i:QH -> PH,                 tau(Q)=tau(P)=t>0
```

from `center-chain-mixed-hecke-overlap-is-common-pauli-source`.  Consider a
canonical-trace matrix sequence, and write `Q_n,P_n,S_(i,n)` for the
corresponding rounded finite-packet operators.  Suppose model-dependent
subprojections `Q_n'<=Q_n`, `P_n'<=P_n` satisfy

```text
tau_n(Q_n-Q_n')+tau_n(P_n-P_n')=eta_n -> 0.            (VLF1)
```

Then the cuts do not define a new corner in the tracial ultraproduct:

```text
||Q_n-Q_n'||_2^2=tau_n(Q_n-Q_n')->0,
||P_n-P_n'||_2^2=tau_n(P_n-P_n')->0.                  (VLF2)
```

Consequently their ultraproduct classes are the fixed regular classes
`Q,P`.  The same is true after intersecting finitely many such source or
range cuts.

Suppose, in addition, that on these cuts the two native selector rows are
authenticated as the restrictions of `S_(1,n),S_(2,n)`, with total ambient
normalized Hilbert--Schmidt error `epsilon_n`, and that the relative polar
factorization is retained as required in
`center-chain-common-source-authenticates-native-covariances`.  On the
common retained source corner the two multiplicity gauges are therefore
unitarily conjugate up to `o(1)+O(epsilon_n)`.  If `t_n'` is its ambient
trace, then `(VLF1)` and the fixed value `t=tau(e)/128` give

```text
t_n'=t-o(1).                                           (VLF3)
```

Normalize the trace on that corner.  The robust affine selector theorem
gives

```text
delta_(1,n)+delta_(2,n) >= 1/3-o(1),                  (VLF4)
```

where the `delta_(i,n)` are the two row defects in the corner-normalized
Hilbert--Schmidt norm.  Returning to ambient normalization yields

```text
epsilon_n >= (1/3-o(1))*sqrt(t_n').                   (VLF5)
```

Equivalently, before absorbing the vanishing polar error,

```text
t_n' <= 9 epsilon_n^2+o(1),
eta_n >= t-9 epsilon_n^2-o(1).                        (VLF6)
```

Thus an `o(1)`-accurate authentication must discard asymptotically **all**
of the fixed common source, not merely a nonvanishing fraction.  In
particular `eta_n=o(1)` and `epsilon_n=o(1)` are impossible along any
canonical microstate sequence.

Thus a representation-dependent cut only differs from the already-refuted
fixed occurrence proposal if it discards asymptotically the whole fixed
Hecke source.  The requested `O(delta^alpha)` loss does not “avoid”
the regular-trace firewall: proving that such a cut follows from vanishing
ordinary relation defect is itself a direct proof that canonical
microstates do not exist.

DERIVATION
vanishing-loss-center-chain-firewall-proof
