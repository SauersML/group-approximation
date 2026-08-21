---
rg: 2
id: extraspecial-spin-predicate-centralization-kills-phase
kind: claim
title: Centralizing a noncentral extraspecial spin word kills the common phase
distinct_from:
  spherical-root-type-selection-is-phase-unsafe: that kills a phase by inconsistent conjugates of a spherical character; this kills it directly from the commutator form of the unique spin packet
  toric-gap-is-a-relative-fd-central-word-face: that proves every player component of a normally imposed toric clause becomes central; this computes the consequence in an extraspecial packet
---

ESTABLISHED.  Let `E` be an extraspecial `2`-group with center
`Z(E)=<J>` of order two.  Every noncentral `p in E` has a commutator witness
`x in E` with

```text
[p,x]=J.                                               (ESP1)
```

This follows from nondegeneracy of the alternating commutator form on
`E/<J>`.

Place `E` inside one player group of a toric presentation and suppose a
clause has player component `p`.  In the quotient by the normal closure of
the clauses, that component is central: for a clause `beta p b`, with `b` in
the other commuting player group,

```text
[beta p b,x]=[p,x]=1.
```

Together with `(ESP1)` this forces `J=1`.  Thus a noncentral Pauli/spin
predicate word cannot be a player component of a phase-safe normally
groupified toric clause when the desired phase is the same extraspecial
center `J`.

## Private conjugators do not repair the packet

Let `t` be a private letter which fixes the common phase, and replace `p` by
`a=t^(-1) p t`.  With `y=t^(-1) x t`,

```text
[a,y]=t^(-1)[p,x]t=J.                                 (ESP2)
```

Centralizing `a` again forces `J=1`.  Hence a Britton/private-letter wrapper
around a single spin predicate, or around its conjugates in a finite clause
cycle, does not evade the firewall.

The only words of `E` surviving this audit are central, hence `1` or `J`, and
cannot carry a nonconstant assignment predicate.  A composite word outside
`E` is not ruled out merely because it contains packet letters, but every
player clause word `a` must satisfy the necessary condition

```text
J notin normalClosure({[a,g]:g in G_player}).          (ESP3)
```

## Balanced Britton words evade phase death but not finite models

There is a genuine distinction between a private conjugate and a balanced
Britton commutator.  In the free extension `E * <t>`, the word `c=[t,p]` can
consistently be set equal to `J`: choose the exact finite spin representation
of `E`, choose `x in E` with `[x,p]=J`, and send `t` to `x`.  Thus

```text
<E,t | [t,p]=J>                                       (ESP4)
```

has an exact finite-dimensional `J=-1` representation.  Its normal closure
does not kill `J`; the map `t |-> x` is already a quotient certificate.

This gives the exact local dichotomy.  A clause which centralizes a conjugate
of a noncentral spin word kills the phase by `(ESP2)`.  Balancing private
letters into a commutator/cycle can carry the phase, but the finite spin packet
itself supplies an exact finite realization.  A family of balanced cycles can
be obstructed only through global incompatibility between the choices of its
private letters.  Proving that every finite-dimensional choice is
incompatible while one tracial choice exists is the central-word state-face
compiler, not a local spin-packet shortcut.  Giving each predicate an
independent private letter is especially powerless: each can be sent
independently to its finite commutator witness.

## Attempts

The audited construction uses the unique `J=-1` spin type as local firewall,
diagonal Alice/Bob packets to choose assignment sectors, and a noncentral
Pauli word as predicate phase.  Type selection on the common game vector is
plausible.  Full normal closure is not: centralization exposes `(ESP1)` and
kills `J`.  Pure conjugation by fresh private letters preserves the witness by
`(ESP2)`.  Balanced commutators avoid phase death, but `(ESP4)` gives their
exact finite spin realization.  The only surviving possibility is a globally
coupled family whose finite inconsistency is the original compiler problem.
