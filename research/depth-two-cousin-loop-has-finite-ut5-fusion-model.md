---
rg: 2
id: depth-two-cousin-loop-has-finite-ut5-fusion-model
kind: claim
title: The shared-arm depth-two cousin loop has a finite UT5 fusion model
distinct_from:
  mixed-steinberg-loops-admit-morita-rectangular-model: that realizes arbitrary typed triangle pastings by rectangular linear maps and leaves source and target objects distinct; this attaches one explicit four-arm cousin loop to the object-erasing three-character fold and both Whitehead address moves.
  fixed-arity-mark-fusion-has-finite-character-model: that fuses only conjugate central marks and optionally separated controlled Pauli payloads; this fuses three genuinely nonabelian UT4 payload packets and makes the same address permutations move every individual payload arm.
  bounded-cousin-checksums-have-finite-clifford-models: that treats central parity checksums and finite affine-symplectic arm permutations; this tests a nested noncommuting coefficient product outside the Pauli/Clifford checksum language.
artifacts:
  - research/depth-two-cousin-ut5-fusion-proof.md
---

**ESTABLISHED EXACT NONCOMMUTING-PAYLOAD COUNTERMODEL.**  Put

```text
u=00,                         v=11,
e_(u,v)=s_u t_v.
```

The literal depth-two Leavitt coefficient identity

```text
t_u e_(u,v) s_v
 =t_u s_u t_v s_v=A                                  (DTL1)
```

uses four shared, address-sensitive arms and returns the active coefficient.
On five consecutive root positions it is the genuinely noncommuting nested
Steinberg word

```text
L_(u,v)
 =[x_12(t_u),
   [x_23(s_u),[x_34(t_v),x_45(s_v)]]]
 =x_15(A)=J.                                           (DTL2)
```

Changing either matched address to a distinct cousin makes the appropriate
inner coefficient product zero and gives the attached crossed-zero word.
Thus `(DTL2)` reads individual row and column payload arms, not merely their
central commutator parity.

Now retain three addressed copies of this whole four-arm loop.  Let their
outputs be `J,C_0,C_1`, let the two Whitehead address moves carry the entire
`J`-packet to the `C_i`-packets arm by arm, and impose the object-erasing
parent fold

```text
C_0C_1=J.                                               (DTL3)
```

This complete table still has an exact finite marked model.  Take three
copies of `UT_5(F_2)`, quotient their product by the diagonal product of the
three central long-root involutions, and let `S_3` permute the copies.  The
three surviving central signs obey `(DTL3)`, the transpositions implement
the Whitehead address moves on every individual noncommuting arm, and each
copy supplies `(DTL2)` by its standard length-three root chain.  The mark
`J` remains nonidentity.

Therefore even the first explicit fixed depth-two relation outside central
parity and finite affine-symplectic Pauli relabeling does not imply `(BAC1)`.
It replaces the three-character/Clifford escape by a finite nilpotent-payload
fusion escape.  A successful relation must couple **different** addressed
payload copies in one noncommuting word; conjugating one complete loop into
three copies and fusing only their central outputs remains finite.

No Property `(T)`, Kazhdan input, stability theorem, or literature result is
used.

DERIVATION
depth-two-cousin-ut5-fusion-proof
