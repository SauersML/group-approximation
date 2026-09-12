---
rg: 2
id: schur-flip-square-exposes-payload-root-word
kind: claim
title: The Schur flip square exposes a payload-tied square-root word on each forbidden atom
distinct_from:
  schur-packet-flips-realize-predicate-cocycle: That records the projective commutator and the resulting multiplicity divisibility; this cancels the packet implementers explicitly and reads the compensating multiplicity phase as one ordinary word on a selected forbidden atom.
  fresh-central-square-lift-is-extension-trivial: That adjoins an unrelated square root; this word is forced by the two predicate-packet flip automorphisms and exists only with the corresponding forbidden Pauli cocycle.
  central-square-orients-transverse-ledger: That consumes a named raw lift; this constructs the named lift.
---

**ESTABLISHED.**  Fix a forbidden selector assignment `a` in the Schur
packet `B_f`, and write `K` for its central Clifford sign.  Let `P_a,Q_a` be
the corrected packet words on that assignment.  They are involutions, they
commute with the selector center, and on the selector atom `A_a` they obey

```text
A_a [P_a,Q_a]=K A_a.                                   (SFR1)
```

Let `alpha_P,alpha_Q` be the two commuting involutive packet flips.  Form the
finite semidirect extension with commuting involutions `u,v` implementing
them.  On the corrected words,

```text
alpha_P(P_a)=K P_a,   alpha_P(Q_a)=Q_a,
alpha_Q(P_a)=P_a,     alpha_Q(Q_a)=K Q_a.              (SFR2)
```

The ordinary group word

```text
d_a=P_a Q_a u v                                      (SFR3)
```

fixes the selector center and satisfies the corner identity

```text
A_a d_a^2=K A_a.                                     (SFR4)
```

More precisely, on a forbidden simple written as packet factor times
external multiplicity, the stable letters have the form

```text
u=Q_a tensor U_0,             v=P_a tensor V_0,
```

and their global commutation forces `U_0 V_0=-V_0 U_0`.  The word `(SFR3)`
acts as

```text
d_a=1 tensor U_0 V_0.                                 (SFR5)
```

It is therefore the raw, phase-sensitive multiplicity holonomy which was
invisible in the projective packet frame, not a freely chosen square-root
gauge.

For every projection `p<=A_a` built from selector and Reynolds averages,
`d_a` commutes with `p` and

```text
(p d_a p)^2=Kp.                                       (SFR6)
```

Fixed finite-table exactification makes the same identities robust in
normalized Hilbert--Schmidt norm with a dimension-independent `C sqrt(E)`
loss.

