---
rg: 2
id: a4-regular-three-way-coherence-transducer-proof
kind: route
title: Principal-angle compression polarizes to three partial unitaries
target: a4-regular-three-way-coherence-transducer
requires:
  - a4-regular-line-sector-spectral-split
  - a4-line-carriers-explicit-idempotents
---

Fix `chi`.  By the line-sector spectral split,

```text
P_chi Q_+ P_chi = E_chi + (1/3) R_chi.                 (1)
```

The total line projection `E=sum E_psi` is central, is contained in `Q_+`, and
is orthogonal to every `R_chi`.  Therefore with `S=Q_+-E`, equation `(1)` gives

```text
R_chi S R_chi = (1/3) R_chi.
```

Hence for `T_chi=sqrt(3) S R_chi`,

```text
T_chi^*T_chi=3 R_chi S R_chi=R_chi.
```

Regular trace bookkeeping gives

```text
tau(R_chi)=tau(P_chi)-tau(E_chi)=1/3-1/12=1/4,
tau(S)=tau(Q_+)-tau(E)=1/2-3/12=1/4.
```

Thus `T_chi` is an isometry from `R_chi` into `S` between equal-dimensional
spaces, so its final projection is all of `S`:

```text
T_chi T_chi^*=S.
```

For distinct `chi,psi`, the identity part of `Q_+=(1+rho(b))/2` has zero
`R_chi`--`R_psi` block, and the line projection `E` is orthogonal to both.
Therefore

```text
T_chi^*T_psi
 = 3 R_chi S R_psi
 = 3 R_chi Q_+ R_psi
 = (3/2) R_chi rho(b) R_psi.
```

Because both `T_chi` and `T_psi` are unitaries onto the same final space `S`,
`T_chi^*T_psi` is a unitary identification from `R_psi` onto `R_chi`.

Finally, restricting `(1)` to `R_chi` and using `Q_+=(1+rho(b))/2` yields

```text
(1/3)R_chi
 = R_chi Q_+ R_chi
 = (1/2)(R_chi+R_chi rho(b) R_chi),
```

so `R_chi rho(b) R_chi=-(1/3)R_chi`.  All identities are stable under regular
amplification because the representation-theoretic decomposition simply
acquires a common multiplicity factor.