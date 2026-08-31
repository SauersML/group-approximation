---
rg: 2
id: bcv-qr-independent-gauge-countermodel-proof
kind: route
title: Put anticommuting multiplicity involutions behind the two BCV sampler sides
target: bcv-qr-cz-and-identity-gauges-remain-independent
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - shared-gauge-cz-cancellation-needs-an-identity-outer-anchor
---

Use the notation of Bowen--Chapman--Vidick, arXiv:2501.00173,
Definition 4.4 and Remark 4.22. We isolate the apparatus obtained by
removing the decision check on the edge `IntroA--IntroB`, or equivalently
by giving that edge the empty linear-constraint list. This is exactly the
case relevant to an automatically accepting candidate anchor.

## 1. The exact block model

Let

```text
H_label = C^(F_2^2),             H_mult = C^2,
e_z = |z><z|,                    z in F_2^2.
```

Put the standard two-qubit Pauli representation on `H_label`, tensored
with the identity on `H_mult`. Write

```text
C_Z = sum_z (-1)^(z_1 z_2) e_z,
V = sigma_z,                     W = sigma_x.             (BQP1)
```

Choose the two linear sampler maps

```text
s_A(z)=z,                        s_B(z)=0.                 (BQP2)
```

At the A-side answer coordinate use the controlled observable

```text
T = sum_z e_z tensor ((-1)^(z_1 z_2)V)
  = C_Z tensor V.                                         (BQP3)
```

At the B-side answer coordinate use

```text
A = sum_z e_z tensor W
  = I tensor W.                                           (BQP4)
```

All other answer coordinates may be deterministic. At `SamZ_A` and
`SamZ_B` use the common PVM `(e_z tensor I)_z`; copy `T` and `A`
respectively to `SamAns`, `Ans`, and `ReadAns`.

These choices satisfy the exact conclusions of BCV Remark 4.22. Equation
(92) is literal. Equation (93) is imposed side by side. Both answer
observables commute with every `SamZ` atom. For the hiding condition,
`ker(s_A)=0`, so there is no nontrivial A-side Pauli-X fibre translation
to check. On the B side `ker(s_B)=F_2^2), and `A=I tensor W` commutes
with every `X^alpha tensor I`. The Read and Hide PVMs are therefore the
ones in BCV equation (98), specialized to these two maps. They are genuine
PVMs by the commutation calculation following that equation. The standard
perfect Pauli-basis PVMs fill the remaining apparatus vertices.

It follows directly, or by running the perfect-completeness construction
separately on the two endpoint families, that every Pauli-basis and
augmentation edge is passed perfectly. The empty check on
`IntroA--IntroB` compares neither endpoint family, so the full
apparatus-plus-autoaccept presentation has value one. Notice the key
logical point in Remark 4.22: equation (93) is

```text
SamAns_A = Ans_A = ReadAns_A
```

and its separate B analogue. There is no A--B equality. Even when two
fibres carry the same decoded source label, the label alone is not an
operator identification.

## 2. Pauli translations preserve the active gauge

For every Pauli label word `p`,

```text
(p tensor I) T (p tensor I)^*
   = (p C_Z p^*) tensor V.                                (BQP5)
```

Thus translation changes only the label representative of the CZ outer
class. More generally, a word in Pauli letters and dressed occurrences of
`T` with occurrence parity `nu` has multiplicity factor `V^nu` and
outer class `[theta]^nu`. Even parity removes both; odd parity retains
both. This is the parity mechanism of
`shared-gauge-cz-cancellation-needs-an-identity-outer-anchor`.
In particular no Pauli-X translation or balanced product produces
`I tensor V`.

The B-side observable in (BQP4) does have identity outer action, but its
gauge is the unconstrained involution `W), not `V).

## 3. There is no hidden positive comparison corner

The two Pauli involutions on `H_mult` anticommute. Hence

```text
(V-W)^2=2I,                       (V+W)^2=2I.              (BQP6)
```

For every multiplicity projection `R`, with normalized trace on
`H_mult`,

```text
||R(V-W)||_2^2
 = tau((V-W)R(V-W))
 = tau(R(V-W)^2)
 = 2 tau(R),                                             (BQP7)

||R(V+W)||_2^2 = 2 tau(R).                              (BQP8)
```

Cyclicity of trace is the only step, so `R` need not reduce `V` or
`W`. Equations (BQP7)--(BQP8) rule out both literal and central-sign
agreement on every nonzero corner. They also give the robust statement:
if either comparison has norm at most `eta`, then
`tau(R)<=eta^2/2`. At zero apparatus defect there can therefore be no
dimension-free positive-corner version of the desired anchor.

Finally, a combinatorial-detyping anchor cannot repair the example.
BCV Definition 4.40 assigns every such anchor both answer lengths zero and
automatically accepts every incident edge. Its measurement algebra is
scalar, so it carries no occurrence of `V), `W`, or any source
unreadable.

A non-autoaccept synchronization equation on a common fibre could of
course identify `V` and `W). But that is an added mixed occurrence
relation. If it is activated only when the readable seed lies in one
fibre, it is exactly the selector-conditioned relation which the
ZPC-to-LCS compiler is trying to replace. The BCV apparatus and its
autoaccept anchors do not make that relation unconditional.
