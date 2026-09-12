---
rg: 2
id: fixed-packet-correction-retains-multiplicity-gauge
kind: claim
title: Fixed-packet HS correction retains an exact stationary multiplicity gauge
distinct_from:
  fixed-packet-spectral-correction-is-gap-or-regular-collapse: that gives the general spectral-cut/functoriality dichotomy for proper-corner decoders; this gives an explicit zero-defect wrong-sector model for packet covariance, commutator, and finite-torsion actuator tests.
  hadamard-selector-commutator-charges-two-path-leakage: that charges the difference of two selector blocks; this proves that their common multiplicity unitary survives every fixed-packet correction and hence cannot be made into a one-sided controlled block.
  amplification-natural-words-cannot-read-packet-multiplicity: that treats arbitrary amplification-natural authenticated words; this isolates the exact Schur-form escape for the type-filtered return actuator and its proposed finite-packet HS correction.
---

# Fixed-packet HS correction retains an exact stationary multiplicity gauge

ESTABLISHED.  Let `F` be a fixed finite packet, let `pi:F->U(V)` be an
irreducible type, and let `alpha` be a packet automorphism implemented
projectively by `C_alpha in U(V)`.  In every exact representation on the
`pi`-isotypic carrier, a unitary actuator satisfying

```text
D pi(f) D^*=pi(alpha(f))        (f in F)                 (FPG1)
```

has Schur form

```text
D=C_alpha tensor W,             W in U(M).               (FPG2)
```

The multiplicity unitary `W` is completely arbitrary.  In particular every
balanced word in actuator variables (commutators, conjugacy relations, and
closed covariance loops) cancels a common scalar or central multiplicity
choice.  If one also imposes finitely many torsion/central-square clauses
`D^m=k`, the multiplicity condition is only `W^m=I`; whenever `m>1`, a
nontrivial scalar root of unity gives an exact stationary model.  Direct
sums allow all permitted roots simultaneously.

For every packet spectral projection `q=e tensor I_M`, the same `W` occurs
on every nonzero selector line of `e`.  Thus no estimate of the form

```text
||(1-q)D(1-q)-(fixed packet block)||_2
 <=omega(packet and covariance defects),                (FPG3)
```

with `omega(0)=0`, can follow from those tests: choose a nontrivial exact
`W` in `(FPG2)`.  This is already a zero-defect matrix countermodel, stable
under amplification.

Fixed-packet HS correction does not help.  Exactification of `F` followed by
averaging onto its covariance intertwiner space lands precisely in

```text
C_alpha tensor M_(dim M),                               (FPG4)
```

and polar correction changes only the arbitrary second tensor factor.  The
stationary model `(FPG2)` is already fixed by this correction.  Hard packet
spectral cuts also have form `e tensor I_M` and cannot distinguish `W`.

The transverse Hadamard charger gives the sharp boundary.  Applied to
`diag(A,B)`, its selector commutator forces `A=B`, but the exact family

```text
A=B=W                                                   (FPG5)
```

has zero leakage and zero charger defect for every `W`.  Hence it synchronizes
two blocks but does not make either block trivial or one-sided.  A
type-filtered actuator still needs a relation with nonzero multiplicity
charge tied to external arithmetic/computation data, or a genuinely
finite-coordinate operation.  Packet correction alone cannot suppress the
wrong-sector block at any cost.

