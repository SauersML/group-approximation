---
rg: 2
id: selector-packet-central-corrector-fails-on-a-three-cycle
kind: claim
title: A three-cycle defeats every packet-central selected-stabilizer corrector
invalidates:
  - centralize-selector-packet-to-wordize-stabilizer-corrector
distinct_from:
  stabilizer-corrector-hermitianizes-zero-compression: that permits an arbitrary unitary stabilizing the one selected projection; this shows that requiring the corrector to centralize the whole finite selector packet is strictly stronger and can be impossible.
  transitive-control-normalizer-forces-projectively-equal-payloads: that is a global multiplicity-orientation obstruction for a transitive normalizer; this is a four-dimensional local obstruction to replacing selected-atom stabilization by packet centralization.
  extraspecial-character-hnn-two-cycle-forces-global-parity: that treats a character-HNN actuator and its global parity consequence; this isolates the earlier centralizer-corrector composition before any such HNN actuator is attached.
---

**ESTABLISHED.**  There are a finite selector group `H`, a selected character
projection `q`, and a payload unitary `W` such that

```text
qWq=0,                                                     (PCC1)
```

but no unitary `S` centralizing the represented copy of `H` makes `SW` an
involution.

Take `H=C_2^2` and represent it on `C^4` as the direct sum of its four
distinct characters.  Let `e_0,e_1,e_2,e_3` be the corresponding joint
character basis, let

```text
q=|e_0><e_0|,
W e_0=e_1,       W e_1=e_2,       W e_2=e_0,       W e_3=e_3.   (PCC2)
```

Then `(PCC1)` is immediate.  Because all four characters are distinct, every
operator commuting with `H` is diagonal in this basis.  Thus, for any
packet-central unitary `S`, write `S e_i=lambda_i e_i`.  The two-step orbit
of `e_0` is then

```text
(SW)^2 e_0=lambda_1 lambda_2 e_2.                         (PCC3)
```

This can never equal `e_0`.  Hence `(SW)^2!=1`.  Equivalently, left
multiplication by a diagonal unitary changes only phases and cannot turn the
three-cycle support of `W` on `e_0,e_1,e_2` into the one- and two-cycle
support of an involution.  This is the promised short cycle-support
obstruction.

The obstruction is exactly centralization, not selected-projection
stabilization.  Indeed put

```text
R=W^*qW=|e_2><e_2|,
V=(the swap of e_0 and e_2, fixing e_1 and e_3),
S_0=V W^*.
```

Then

```text
S_0 q S_0^*=q,             S_0 W=V=V^*=V^-1,             qVq=0. (PCC4)
```

Thus the unrestricted corrector from
`stabilizer-corrector-hermitianizes-zero-compression` works exactly as
claimed.  Here `S_0` swaps the two distinct character lines `e_1,e_2`, so it
does not centralize `H`; in fact that swap normalizes the full `C_2^2`
character packet.  Consequently this example does **not** refute a
normalizer-based wordization, an unrestricted selected-atom stabilizer, or
the remaining typewise payload-sensitive nontransport holonomy readout.  It
invalidates only the specifically named shortcut which replaces “stabilize
`q`” by `[S,H]=1`.
