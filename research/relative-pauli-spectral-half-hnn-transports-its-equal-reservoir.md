---
rg: 2
id: relative-pauli-spectral-half-hnn-transports-its-equal-reservoir
kind: claim
title: An HNN edge addressing one relative-Pauli half transports its equal reservoir too
distinct_from:
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that proves conjugacy cannot turn two baseline copies into one full packet; this uses the fixed relative-Pauli support words and shows why transporting the active half does not delete its exit half.
  raw-radical-full-scale-merge-needs-an-equal-reservoir: that gives the dimension ceiling for four commuting radical branches; this treats the anticommuting relative-Pauli split where the two support projections themselves are literal spectral halves.
  relative-pauli-child-split-gives-one-exit-copy: that positively names the active and exit halves; this audits the proposed one-sided HNN return of the active half.
---

Let `A` be the finite baseline packet and let `Q` be an involution commuting
with `A`.  Suppose another packet word `P` commutes with `A` and satisfies
`PQ=-QP` on the selected carrier.  Put

```text
e_+=(1+Q)/2,             e_-=(1-Q)/2.                  (RPH1)
```

Then `P e_+ P^*=e_-`, so the two `A`-carriers have equal dimension and
equal normalized trace in every finite exact packet representation.

Now let a stable letter `t` implement an isomorphism from a finite edge
subgroup containing `A` and `Q` to a target subgroup, with

```text
tQt^*=Q'.                                                (RPH2)
```

Functional calculus inside the finite group algebra gives exactly

```text
t e_+ t^*=e'_+,             t e_- t^*=e'_- .           (RPH3)
```

Thus an ordinary HNN edge which can address the active half necessarily
transports the exit half as a second, equally large target reservoir.  It
cannot map `e_+` to one fresh baseline packet while deleting `e_-` or making
it dimensionless.  Omitting `Q` from the edge avoids `(RPH3)` only by losing
all group-word control of which half is active.

The conclusion persists for an injective finite edge map rather than an
isomorphism onto a named copy: `e_+` and `e_-` map to the two spectral
projections of the image of `Q`, and unitary conjugacy preserves both source
dimensions.  Additional finite packet charts may permute or split the two
target types, but their total carrier dimension remains the sum of both
halves; the regular stationary flow records precisely this reservoir.

## Boundary of the no-go

A genuine one-sided compression by an infinite subgroup can compare two
different invariant projections rather than conjugating the two spectral
halves.  To use it here one must additionally force, on the same selected
carrier, an equality of the form

```text
e_+ = projection onto L-fixed vectors,
e_+ + e_- = projection onto L_0-fixed vectors,          (RPH4)
```

for a proper conjugate `L_0<L` (with orientation adjusted as needed).
Property `(T)` could then make the comparison robust and finite trace would
pay `tau(e_-)`.

But `(RPH4)` is not a consequence of the literal words `P,Q`.  It is a
character-conditioned attachment of an infinite actor to one finite packet
half.  Ordinary subgroup conjugacy attaches to both characters, while a
finite packet attachment has the exact stationary countermodel above.
Hence `(RPH4)` is the sharpened positive target: a normalized-HS robust
spectral-half/invariant-projection identification, equivalently the
one-sided charged proper-corner section.
