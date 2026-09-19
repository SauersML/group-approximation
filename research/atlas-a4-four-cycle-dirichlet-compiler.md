---
rg: 2
id: atlas-a4-four-cycle-dirichlet-compiler
kind: claim
title: One scalar four-transvection Dirichlet energy is enough to compile the A4 atlas
distinct_from:
  atlas-a4-four-cycle-trace-compiler: that stronger target transfers the collision trace separately to three leaf traces; this target asks only for the final sum of four trace deficits.
  atlas-a4-relative-packet-commutator-collapse: that stronger target controls ten packet-letter commutators; this target controls only the minimal four-transvection generating cycle.
---

For the normalized exact-regular A4 context network, let

```text
T={t01,t12,t23,t30},
V_n(t)=U_n lambda_(k_n)(t)U_n^*lambda_(k_n)(t)^*.
```

Prove one constant `C_D<infinity`, independent of `n` and of the external
multiplicity, such that

```text
sum_(t in T) (1-Re tau_n(V_n(t)))
 <= C_D (||sigma_n(q_19243)-1||_2 + eta_n).             (A4-DIR)
```

That single scalar inequality is the complete compiler interface.  Since

```text
2(1-Re tau_n(V_n(t)))
 = ||V_n(t)-1||_2^2
 = ||[U_n,lambda_(k_n)(t)]||_2^2,
```

`(A4-DIR)` is exactly a dimension-free bound on the minimal four-generator
conjugation Dirichlet energy of the relative chart frame.  The established
four-cycle A8 commutant gap converts it directly to chart-frame collapse.

No individual leaf trace, hub-to-leaf transport, chart alignment, matrix-valued
holonomy, or approximate A8 representation has to be recovered.

## Attempts

- **Search for one cyclic SOS identity.**  After the fixed A4 qutrit split and
  the `K_(2,2) disjoint_union K_(2,4)` tree gauge, write the left side as a
  quadratic trace functional of the four residual rectangle holonomies.  The
  desired proof can be one positive-semidefinite comparison with packet and
  collision residual energies.
- **Use a dual certificate.**  Treat `(A4-DIR)` as a finite noncommutative
  Poincare inequality.  A failed candidate PSD comparison should return a
  finite-dimensional dual vector/state showing which multiplicity mode escapes;
  feed that mode back into the packet search instead of guessing gauges.
- **Exploit the minimal generating set.**  There is no downstream benefit to
  controlling any packet letter outside `T`: `atlas-a8-four-cycle-commutant-gap`
  already turns exactly these four energies into distance from the full A8
  commutant.
- **Scalarize before synchronizing.**  Local qutrit-wire gauges may differ from
  context to context.  Because only a trace Dirichlet form is retained, average
  or pinch those gauges before attempting any operator-valued synchronization.
