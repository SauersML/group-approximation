---
rg: 2
id: same-center-m8-commutators-cannot-wordize-one-eighth-reflection
kind: claim
title: Two-word commutators on the same-center M8 packet cannot wordize the one-eighth reflection
artifacts:
  - research/same-center-m8-commutator-determinant-proof.md
distinct_from:
  packet-controller-orbit-products-have-orientation-dichotomy: that treats products of conjugates of one rank-one controller and separates even gauge cancellation from odd determinant failure; this rules out manufacturing the controller itself as a commutator of two native packet or Whitehead occurrences.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that classifies parity of repeated occurrences of one CZ-outer implementer and identifies a positive identity-outer anchor; this gives the determinant and label-rank obstruction before such an anchor is available.
  leavitt-crossed-gram-pauli-charge-has-sectorwise-escape: that permits independently varying gauges on four selector sectors and cancels the controlled phase there; this already fails on one irreducible eight-dimensional label, even if the multiplicity commutator were trivial.
---

**ESTABLISHED SCOPED FENCE.**  Work on the common marked carrier of
`same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps`, whose label
algebra is `M_8(C)`.  Let

```text
C_(1/8)=1-2E,                    rank(E)=1.             (MCO1)
```

No two label unitaries `A,B in U(8)` satisfy

```text
[A,B]=C_(1/8).                                          (MCO2)
```

Indeed every ordinary commutator has determinant one, whereas

```text
det(C_(1/8))=-1.                                       (MCO3)
```

The concrete controlled-Pauli AND attempt stops one dyadic scale earlier.
Take two independent half-control projections `P,Q` on the first two label
qubits and a Pauli pair `X,Z` on the third.  The controlled gates

```text
U_P=(1-P)+PX,              V_Q=(1-Q)+QZ                (MCO4)
```

have label commutator

```text
[U_P,V_Q]=1-2PQ.                                       (MCO5)
```

But `PQ` leaves the two-dimensional payload qubit free, so

```text
rank(PQ)=2,              negative_fraction([U_P,V_Q])=2/8=1/4. (MCO6)
```

Obtaining rank one by the same formula requires one control to be a joint
two-bit atom, so one of the two gates must already contain the missing
three-bit controlled occurrence.  This is circular rather than a
wordization of `C_(1/8)` from the established Pauli and Whitehead words.

The adjacent Whitehead braid does not cancel the remaining multiplicity
commutator.  On the common carrier write

```text
W_1=SWAP_(1,2) tensor V_1,
W_2=SWAP_(2,3) tensor V_2.                             (MCO7)
```

The braid proves only

```text
V_1V_2V_1=V_2V_1V_2,                                  (MCO8)
```

not `[V_1,V_2]=1`.  The two standard transpositions in `S_3` satisfy
`(MCO8)` and have a nontrivial order-three commutator.  Consequently
`controlled-pauli-commutator-is-and-times-multiplicity-commutator` cannot
remove the external factor by appealing to the braid.

More generally, a literal common implementer can make the two multiplicity
factors equal only inside one packet outer-automorphism class.  The two
controlled Pauli actions used by the AND construction have different
symplectic outer actions, as recorded by
`packet-dressed-shared-implementer-requires-one-outer-class`.

Thus no ordinary two-word commutator of the established same-center Pauli or
adjacent-Whitehead occurrences supplies the required one-eighth selector
label.  The surviving target is a noncommutator, odd-determinant native
occurrence directly typed as

```text
C_(1/8) tensor V_2                                    (MCO9)
```

on a positive model-dependent subcorner, or an independently authenticated
identity-outer occurrence `I tensor V_2` sharing its gauge.  The claim does
not rule out such a new mixed, scale-changing occurrence.

DERIVATION
same-center-m8-commutator-determinant-proof
