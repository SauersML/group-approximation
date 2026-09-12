---
rg: 2
id: orientation-graded-mixed-returns-have-a-balanced-double
kind: claim
title: An orientation-graded mixed return always has an exact balanced double
distinct_from:
  controlled-reflection-cell-has-free-orientation: that classifies the local multiplicity involution; this shows that every larger exact mixed-return presentation retaining the orientation grading inherits a balanced marked representation.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that tracks cancellation in fixed controlled words; this is a representation-theoretic tensoring firewall for arbitrary additional relations.
  balanced-controlled-whitehead-return-checksum: that quantifies the return leakage once the balanced sector occurs; this proves when the balanced sector cannot be removed by mixed relations.
---

**ESTABLISHED.**  Let `Gamma` contain the controlled Pauli group

```text
G=P semidirect <t>,
```

with central mark `J`, and suppose the proposed mixed-return presentation
retains a homomorphism

```text
chi:Gamma -> C_2,
chi(P)=chi(J)=0,       chi(t)=1.                        (OGM1)
```

If `rho_0` is any exact finite-dimensional marked representation of
`Gamma`, then

```text
rho(g)=rho_0(g) tensor diag(1,(-1)^chi(g))              (OGM2)
```

is another exact marked representation.  On every literal controlled-spin
summand of `rho_0`, its restriction to `G` contains the two orientations
with equal multiplicity:

```text
rho(p)=S(p) tensor I_2,
rho(t)=C tensor diag(1,-1),
mu=0.                                                   (OGM3)
```

Every even-grade Whitehead actuator `W in ker(chi)` acts trivially on the
new orientation factor.  Hence adjoining arbitrarily many exact relations
that preserve `(OGM1)` cannot select the literal fine reflection or identify
the controlled and Pauli Reynolds ranges.  In the doubled representation
their normalized ranks still differ by exactly `1/32`, and
`balanced-controlled-whitehead-return-checksum` gives that much returned
adjoint leakage for every `W`.

Therefore a successful mixed Whitehead compiler must do at least one of the
following:

1. destroy the orientation grading through an odd selector coupling;
2. arrange that no exact finite-dimensional marked representation survives
   the full presentation; or
3. use a genuinely finite-matrix/canonical-coordinate estimate that is not
   a consequence of the orientation-graded exact relations alone.

In particular, adding further even Steinberg triangles, even Whitehead
loops, or covariance relations while leaving `(OGM1)` intact cannot prove
the missing Reynolds return.

Breaking the grading by the most obvious single odd equality does not evade
the obstruction.  `odd-selector-row-balances-or-kills-outer-action`
shows that `t=W r W^*` has an exact balanced marked countermodel and in fact
forces `mu` toward zero in approximate models.  Strengthening it by making
`W` a full packet normalizer instead destroys the controlled outer action.

Moreover, `normal-pauli-extensions-retain-the-orientation-character` shows
that `(OGM1)` is automatic in **every** ambient group in which the marked
two-qubit Pauli packet remains normal: compose its symplectic outer action
with the product-sign character of
`O_4^+(F_2)~=(S_3 x S_3) semidirect C_2`.  Hence the successful Whitehead actuator
must genuinely move the packet to another scale rather than live in any
larger normalizer.
