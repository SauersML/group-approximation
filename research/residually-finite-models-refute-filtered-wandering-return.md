---
rg: 2
id: residually-finite-models-refute-filtered-wandering-return
kind: claim
title: Residually finite models exactly refute a positive filtered wandering return
distinct_from:
  amenable-edge-hnn-preserves-hyperlinearity: that gives an asymptotic permanence obstruction for every amenable-edge HNN extension; this constructs zero-defect finite quotient countermodels to the filtered moment itself.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that describes compatible representation-type multiplicities; this directly evaluates the proposed wandering moment in a separating finite quotient.
  one-filtered-wandering-return-is-already-nonhyperlinearity: that uses arbitrary canonical hyperlinear microstates; this gives an exact obstruction whenever the ambient group is residually finite.
---

Let `Gamma` be residually finite, let `H<=Gamma` be finite, let
`0!=P in C[H]` be a projection, and write

```text
P=sum_(g in H) a_g g.
```

Suppose `r in Gamma` satisfies

```text
g r != 1                 whenever a_g!=0.             (RFW1)
```

Then for every finite word window `W` there is an exact finite-dimensional
representation `rho_W` which has canonical trace on `W`, is faithful on
`H`, and satisfies

```text
tr(rho_W(P))=tau_H(P)>0,
tr(rho_W(P r))=0.                                     (RFW2)
```

Consequently no positive dimension-independent inequality

```text
Re tr(P(U)r(U)) >= c tr(P(U))-omega(def(U)),
c>0,       omega(0)=0,                                (RFW3)
```

can hold for all sufficiently canonical finite matrix models of `Gamma`.

## Proof

Enlarge the finite set to be separated so that it contains every nonidentity
element of `H`, every nonidentity word in `W`, and every `g r` occurring in
`(RFW1)`.  Residual finiteness supplies a finite quotient

```text
phi:Gamma->Q
```

in which all these elements remain nonidentity.  In particular `phi` is
injective on `H`.  Use the normalized left regular representation of `Q`.
Its restriction to `H` is `[Q:H]` copies of the regular representation of
`H`, so

```text
tr_Q(phi(P))=tau_H(P).
```

Moreover

```text
tr_Q(phi(P r))
 =sum_g a_g tr_Q(phi(g r))
 =0,
```

because every support word remains nonidentity.  The same regular trace is
zero on every nonidentity word in `W`, and all presentation relators hold
exactly.  This proves `(RFW2)` and contradicts `(RFW3)`.

Taking an exhausting sequence of windows gives a canonical microstate
sequence.  Thus the proposed two-partial-swap/HNN actuator cannot live in a
residually finite Bass--Serre extension.  In particular a finite graph of
finite packet groups, which is virtually free, is ruled out not merely by a
stationary-flow heuristic but by exact zero-defect countermodels for the
specific filtered moment.  Together with
`amenable-edge-hnn-preserves-hyperlinearity`, this excludes every
finite/amenable-edge HNN attempt over a hyperlinear base.
