---
rg: 2
id: one-bit-selector-cannot-orient-paired-frame-hard-cycle
kind: claim
title: The Clifford half-selector cannot orient the paired-frame hard two-cycle
distinct_from:
  one-bit-clifford-selector-halves-a-chosen-bcs-atom: That proves the selector retains half of one forbidden atom; this proves that the same Pauli bit cannot also provide one-sided ownership for the support-packet Reynolds detector.
  gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap: That treats an abstract equal-weight gauge orbit; this identifies the equal-weight orbit forced by the concrete one-bit selector relations.
  paired-frame-hard-characters-form-forced-two-cycle: That classifies every finite packet edge; this couples the forced two-cycle to the selector flip and computes the resulting loss of orientation.
---

**ESTABLISHED FIREWALL.**  Work on one forbidden assignment carrier
`E=QP_(c,a)` in the setup of
`one-bit-clifford-selector-halves-a-chosen-bcs-atom`.  Write

```text
e_+=(1+p)/2,                 e_-=(1-p)/2.
```

The selector relation gives `q p q=-p` on `E`, while `q` commutes with
`E`.  Hence

```text
q E e_+ q^*=E e_-,          tau(Ee_+)=tau(Ee_-)=tau(E)/2.       (SPC1)
```

Suppose one tries to reuse this sign as the missing ownership coordinate of
the paired support frame: the `e_+` half carries the hard character
`h=101`, the `e_-` half carries `h'=011`, and covariance of the framed packet
under `q` implements the packet automorphism `alpha` with

```text
alpha: h <--> h'.                                             (SPC2)
```

Then every reducing carrier for the selector contains the two framed hard
sectors with equal multiplicity.  On that carrier the plus and minus
commutant modules are therefore

```text
C_+(h)^m directSum C_+(h')^m,
C_-(h)^m directSum C_-(h')^m.                                (SPC3)
```

They are unitarily conjugate by
`gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap`.  Consequently the
oriented `1/98` deficit of
`paired-frame-forbidden-scalar-overlap-gap` vanishes on the selector-reducing
carrier.  The selector supplies a named positive half, but its flip supplies
the reverse reservoir with exactly the same mass.

If covariance `(SPC2)` is omitted, the sign of `p` is not authenticated as a
packet central character at all, so it gives no Reynolds ownership
inequality.  Thus the two possible uses are exhaustive for this literal
coupling: uncoupled selector signs do not own the hard frame, while covariant
selector signs symmetrize its forced two-cycle.

The one-type reduction remains valid and useful, but the escape actuator
still needs a label not returned by the finite selector group—for example a
one-sided level, first-hit boundary, or another genuinely nonstationary
coordinate.
