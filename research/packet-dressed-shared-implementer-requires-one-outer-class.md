---
rg: 2
id: packet-dressed-shared-implementer-requires-one-outer-class
kind: claim
title: Packet dressing shares a multiplicity implementer only within one outer-automorphism class
distinct_from:
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that isolates the unwanted external commutator for two independent controlled gates; this characterizes the tempting one-stable-letter cancellation and its exact algebraic limitation.
  commuting-automorphism-cocycle-forces-multiplicity: that uses two commuting outer actions and their projective lifts to force divisibility; this concerns two lifts obtained from one stable letter by packet dressing, which necessarily have the same outer action.
  controlled-pauli-corner-has-clifford-groupification: that groupifies one controlled covariance with an arbitrary multiplicity involution; this proves that two different Pauli covariances cannot generally reuse that involution through packet words.
---

Let `B` be a group embedded in an extension, let `u` normalize `B` by
`alpha in Aut(B)`, and consider a second word

```text
v=h u k,                    h,k in B.                    (DSI1)
```

Then the automorphism induced by `v` is

```text
beta=Inn(h alpha(k)) o alpha.                            (DSI2)
```

In particular

```text
[beta]=[alpha] in Out(B).                                (DSI3)
```

Conversely, if `beta=Inn(c)o alpha`, the choice `v=c u` realizes it.  Thus
packet dressing realizes exactly one outer-automorphism class.

On a `B`-isotypic carrier `T tensor M` fixed by `alpha`, write

```text
rho(u)=C_alpha tensor R.
```

Equation `(DSI1)` forces

```text
rho(v)=rho_T(h alpha(k)) C_alpha tensor R,               (DSI4)
```

so the two gates do share the same external multiplicity unitary.  Their
commutator has no external factor.  This is a valid cancellation mechanism,
but `(DSI3)` is unavoidable when the copy of `B` remains embedded.

For an extraspecial Pauli packet, every inner automorphism acts trivially on
the elementary abelian quotient `B/Z(B)`.  Hence two Clifford covariances
with different induced symplectic maps on that quotient represent different
outer classes and cannot be related as in `(DSI1)`.  In particular the
standard controlled-X and controlled-Z/CZ covariances used in the two-gate
AND construction have different quotient actions.  The direct attempt to
cancel `(CPM4)` by expressing both as packet dressings of one implementer
therefore fails for the basic Pauli cell.

This does not exclude a larger packet in which two nonlinear gate lifts lie
in one outer class, nor a holonomy relation which directly controls two
independent multiplicity factors.
