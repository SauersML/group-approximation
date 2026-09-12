---
rg: 2
id: character-hnn-retains-and-or-holonomy
kind: claim
title: Finite-character HNN transport preserves the AND cocycle or leaves relative holonomy
invalidates:
  - zpc-identity-copy-via-character-hnn-transport
distinct_from:
  reynolds-exit-does-not-carry-pauli-gauge: that treats the index-two section whose assignment mass is an unused range; this treats exact character transport when the selected atom itself is a source.
  pauli-gauge-word-retains-and-cocycle: that treats dressing inside one packet; this treats transport of the packet by one or two HNN edges.
  finite-character-idempotents-have-exact-hnn-transport: that proves atoms can be transported exactly; this proves atom transport alone does not convert an active controlled actor into an authenticated identity-label copy.
---

**ESTABLISHED CHARACTER-HNN FIREWALL.**  Exact finite-character HNN
transport does not instantiate the active/identity-copy seam by either of
its natural forms.

If one stable letter `t` transports the full controlled-Pauli packet and both
actors, conjugating the covariance row gives

```text
(tUt^-1)(tZt^-1)(tUt^-1)
 =(tSt^-1)(tZt^-1).                                    (CHH1)
```

Thus an active source character remains active relative to the transported
control.  The same is true for the second actor, and

```text
t[U,V]t^-1=[tUt^-1,tVt^-1].                            (CHH2)
```

After stripping the transported Pauli labels, the same AND cocycle and the
same gauge commutator remain.  Relabelling a target selector by `J` changes
its displayed character but not the transported covariance equation.

If the common edge transports only the actors and omits the Pauli/control
packet, it may make their target labels look trivial, but it preserves only
the full operator spectra.  The source Pauli factors can be absorbed into
target multiplicity by Morita exchange, so the target gauges are not
identified with `A_11,B_11`.  Packet omitted means no gauge authentication;
packet included means no conversion to identity action.

Using two separate edges `t_A,t_B` leaves the relative holonomy.  Orthogonal
target character atoms give zero cross-Gram.  On a common target atom `p`,
the mixed moment contains the compressed relative stable word

```text
p t_A^* t_B p,                                          (CHH3)
```

which is an arbitrary source-commutant unitary.  Character moments and the
two separate conjugacy tables do not constrain it.  Even positive or maximal
cross-Gram does not force its gauge factors to commute without a further
mixed phase row.

Consequently exact atom transport yields the dichotomy: a common edge
preserves the controlled cocycle, while separate edges retain arbitrary
relative holonomy.  This does not refute a new mixed occurrence relation
which explicitly controls `(CHH3)`.
