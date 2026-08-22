---
rg: 2
id: atlas-e12-binary-extremal-is-a-finite-residual-test
kind: claim
title: Realizing the sharp e12-only root pattern is exactly one omitted-bridge finite-residual test
artifacts:
  - experiments/atlas_a4_packet_19243_quotient.py
  - experiments/atlas_a8_minimal_transvection_cycle.py
distinct_from:
  atlas-root-ellipse-is-amplification-concave: that proves the binary pattern is the sharp scalar extremizer; this identifies the exact quotient-theoretic condition for realizing that pattern.
  atlas-a4-finite-quotient-escape-fence: that starts with an arbitrary nontrivial finite quotient and gets F at least one; this asks whether equality can occur with precisely one surviving cycle bridge.
---

Let

```text
Gamma_A4=(A8*A8)/<<thirty packet words,q_19243>>
```

and write

```text
w_ij=i_2(t_ij)i_1(t_ij)^(-1).
```

Form the three-bridge quotient

```text
Q_12=Gamma_A4/<<w_01,w_23,w_30>>.                     (E12-QUOT-1)
```

Then the sharp binary energy pattern

```text
(e_01,e_12,e_23,e_30)=(0,1,0,0)                      (E12-QUOT-2)
```

is realized by a regular representation of an actual finite packet/collision
quotient if and only if `Q_12` has a finite quotient in which the image of
`w_12` is nonidentity.  Equivalently,

```text
w_12 is not in the finite residual of Q_12.            (E12-QUOT-3)
```

Thus equality in the amplified finite-quotient fence is neither a free scalar
choice nor ruled out by the four-cycle generation theorem.  Inside one chart,

```text
<t_01,t_23,t_30>
```

has order `64` and does not contain `t_12`; identifying those three chart
copies gives no chart-local word proof of the fourth equality.

The quotient exporter now accepts

```text
--identify-cycle-except t12
```

and tests the omitted bridge in exactly `(E12-QUOT-1)`.  A bounded GAP run on
MSI reached coset-table enlargement rather than a decision and was terminated.
No finiteness, infinitude, survival, or collapse conclusion is inferred from
that computational outcome.  The rigorous result is the finite-residual
reduction `(E12-QUOT-3)` and the exact order-`64` exclusion above.

