---
rg: 2
id: atlas-a4-four-cycle-trace-compiler
kind: claim
title: Four scalar covariance traces and collision 19243 suffice for the A8 holonomy gap
artifacts:
  - experiments/atlas_a4_classical_two_holonomy_profile.py
  - experiments/atlas_a8_four_cycle_raw_s3.py
  - experiments/atlas-word-19243.json
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

## Common-frame scalar audit

The recently refuted `atlas-a4-componentwise-commutant-collapse` cannot be
used here.  In fact `q_19243(U_n)->1` forces the common relative frame a fixed
distance from the collision `S3` commutant.  Thus neither `(A4-TRACE-1)` nor
`(A4-TRACE-2)` may be justified by first projecting `U_n` to a packet-component
commutant.  The scalar traces must be read directly from the shifted
centralizer-product realization of the same `U_n`.

There is a finite exact obstruction to an even more tempting shortcut:
`(A4-TRACE-1)` is not a packet-only inequality.  In the natural 15-point
permutation representation, take the inner classical packet alignment

```text
g = 00000101010000000001000000000001.
```

Exact substitution into the thirty packet words gives zero packet residual.
For the covariance cocycles of the four transvections, the exact squared-defect
numerators (with common denominator `15`) are

```text
                 t01   t12   t23   t30
15 ||V(t)-1||_2^2 24    24    16    24.               (A4-TRACE-SCREEN)
```

Because `Re tau(V)=1-||V-1||_2^2/2`, this position has

```text
3 Re tau(V(t23))
 -Re tau(V(t01))-Re tau(V(t12))-Re tau(V(t30))
 = (24+24+24-3*16)/(2*15)
 =4/5>0.                                               (A4-TRACE-FAIL)
```

The collision squared-defect numerator at the same position is `16`, so it
does not satisfy the asymptotic collision hypothesis.  Consequently
`(A4-TRACE-FAIL)` does **not** refute the present joint claim.  It does prove
that trace invariance alone cannot erase the collision from the leaf-transfer
step: the thirty shifted packet constraints, even exactly, do not imply
nonpositive average transfer.

The minimal viable common-frame scalar inequality is therefore the joint
estimate

```text
3 Re tau(V(b))-sum_(t in {t01,t12,t30}) Re tau(V(t))
 <= C_joint (||q_19243(U)-1||_2+eta).                 (A4-TRACE-JOINT)
```

Together with `(A4-TRACE-2)`, `(A4-TRACE-JOINT)` is sufficient for every
downstream asymptotic use of `(A4-TRACE-1)`, because both residuals tend to
zero.  The explicit screen calibrates any pointwise branch-blind coefficient:
at the displayed position it must satisfy

```text
C_joint >= (4/5)/sqrt(16/15)=sqrt(3/5).
```

Equivalently one may combine the hub readout and leaf transfer into the single
Dirichlet estimate already named `atlas-a4-four-cycle-dirichlet-compiler`;
no duplicate target is needed.  What remains missing here is a cyclic trace
identity for `(A4-TRACE-JOINT)` which retains the fact that all thirty shifted
factorizations use one common `U`.  The four rectangle invariants alone lose
one independent component-root gauge and cannot supply that identity.

Accordingly this claim remains open.  The exact scalar hole is now isolated:
derive `(A4-TRACE-JOINT)` directly from common-`U` liftability and collision,
without any component-centrality inference.
