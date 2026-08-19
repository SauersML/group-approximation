---
rg: 2
id: atlas-a4-four-cycle-trace-compiler
kind: claim
title: Four scalar covariance traces and collision 19243 suffice for the A8 holonomy gap
distinct_from:
  atlas-a4-normal-certificate-compiler: that stronger target constructs three operator-valued conjugacy transports; this target asks only for one averaged real-trace inequality plus one scalar collision readout.
  atlas-a4-alignment-moment-simplex-rounding: that rounds thirty-one kernel-word moments to a 40320-point classical simplex; this target keeps only the four transvection coboundary moments used by the final commutant Poincare inequality.
---

Use the minimal four-transvection cycle

```text
T={t01,t12,t23,t30},
b=t23,
```

and for a normalized exact-regular A4 context network put

```text
V_n(t)=U_n lambda_(k_n)(t) U_n^* lambda_(k_n)(t)^*.
```

It is enough to prove constants `C_tr,C_col<infinity`, independent of `n` and
of the external multiplicity, such that

```text
3 Re tau_n(V_n(b))
 - sum_(t in {t01,t12,t30}) Re tau_n(V_n(t))
 <= C_tr eta_n,                                         (A4-TRACE-1)

1-Re tau_n(V_n(b))
 <= C_col (||sigma_n(q_19243)-1||_2 + eta_n).           (A4-TRACE-2)
```

No transport unitaries, multiplication table, approximate representation, or
choice of chart-alignment sector is part of the interface.  The first line is
one scalar **average trace transfer** from the collision transvection to the
three other transvection opcodes; the second is one scalar collision readout.

The point is that normalized Hilbert--Schmidt commutator energy is itself a
trace observable:

```text
||V_n(t)-1||_2^2 = 2-2 Re tau_n(V_n(t)).
```

Thus `unitary-trace-energy-transfer` converts `(A4-TRACE-1)` into control of the
sum of the three leaf energies, while `(A4-TRACE-2)` controls the hub energy.
The established four-cycle A8 commutant gap then does the operator-valued
rounding for free.

## Attempts

- **Finite tracial SOS, not transport synthesis.**  After the canonical A4
  qutrit/multiplicity split, search directly for a cyclic sum-of-squares
  certificate of `(A4-TRACE-1)` and `(A4-TRACE-2)` in the four rectangle
  holonomies.  Only scalar traces survive, so off-diagonal multiplicity gauges
  may be averaged away rather than reconstructed.
- **Connection-Laplacian Dirichlet form.**  The left side needed downstream is
  the four-generator conjugation Dirichlet energy of `U_n`.  Seek a fixed PSD
  comparison between that Dirichlet form and the packet/collision residual
  form after tree gauge; tensor amplification cannot change a finite PSD
  generalized eigenvalue.
- **Exploit trace invariance aggressively.**  Any local argument that produces
  a conjugate of `V_n(b)` need not identify the conjugator: taking trace erases
  it.  Likewise three different local gauges may be used for the three leaves
  with no cross-gauge consistency condition.
- **Search only five observables.**  The compiler sees the four real traces
  `Re tau(V_n(t))` and the collision defect.  Do not round the thirty pair-cube
  moments or a full finite alignment distribution unless a separating
  functional actually uses them.
