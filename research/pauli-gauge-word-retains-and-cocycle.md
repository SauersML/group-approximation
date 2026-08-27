---
rg: 2
id: pauli-gauge-word-retains-and-cocycle
kind: claim
title: Packet dressing cannot separate the controlled-Pauli gauge commutator from its AND cocycle
invalidates:
  - zpc-two-label-copy-gauge-strip-by-packet-dressing
distinct_from:
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that computes the undressed controlled commutator; this proves the nonlinear phase survives every fixed Pauli-packet dressing of a word carrying the same gauge commutator.
  transitive-selector-flips-kill-leavitt-sibling-support: that rules out rank-preserving transport between forbidden and allowed selector atoms; this rules out manufacturing a pure gauge word inside each atom by packet dressing alone.
  finite-packet-functoriality-has-positive-regular-profile: that is a global regular-profile obstruction; this is the local Pauli-cocycle calculation identifying the unavoidable quadratic term.
---

**ESTABLISHED PACKET-DRESSING FIREWALL.**  Work on one marked
Pauli/selector sector and write

```text
U=X^a tensor A,              V=Z^b tensor B,
a,b in F_2,                 [X,Z]=J.                    (PDC1)
```

Every fixed packet letter acts only on the label factor.  Let `W` be an
ordinary word in those packet letters and `U,V`.  Suppose that after deleting
the fixed packet letters and reducing the remaining word in `C_2*C_2`, its
gauge part is

```text
[A,B]=ABAB.                                                (PDC2)
```

If the label part of `W` is scalar, then there are fixed
`lambda,mu,nu in F_2` such that

```text
W_label(a,b)=J^(ab+lambda a+mu b+nu).                     (PDC3)
```

In particular, no such packet-dressed word equals
`I_label tensor [A,B]` on all four selector sectors.

To prove this, encode each Pauli label letter by a vector in `F_2^2`.
Multiplication carries the standard Pauli central two-cocycle, whose
polarization is the alternating form.  Each occurrence of `U` contributes
`a e_X`, each occurrence of `V` contributes `b e_Z`, and a fixed packet
letter contributes a constant vector.  Therefore the central exponent is a
polynomial of degree at most two in `a,b`.  Fixed--variable pairs contribute
only linear terms, fixed--fixed pairs contribute a constant, and equal
variable pairs contribute only `a^2=a` or `b^2=b`.  The coefficient of `ab`
is the mod-two crossing number of `U` and `V` in the deletion word.

Deleting an adjacent `UU` or `VV` pair does not change that crossing number:
every occurrence of the other variable crosses the two deleted equal letters
twice.  Reduction to `(PDC2)` therefore leaves the crossing number of
`UVUV`, which is one because

```text
X^a Z^b X^a Z^b=J^(ab).                                  (PDC4)
```

Once the noncentral label part is assumed to vanish, `(PDC3)` follows.

The obstruction also covers every finite family of dressed comparisons.
Relative to the native row, row `i` has inconsistency set
`ell_i(a,b)=1` for an affine function `ell_i`.  If every added row remains
consistent on the three allowed points `00,10,01`, then every `ell_i`
vanishes on three affinely independent points and hence is identically zero;
it also vanishes at `11`.  No finite family can isolate only the AND atom.

The simplest proposed identity copies show the obstruction exactly.  Taking
`XU` and `ZV` gives

```text
[XU,ZV]=J^((a+1)(b+1)) tensor [A,B],                     (PDC5)
```

whereas `[U,V]=J^(ab) tensor [A,B]`.  Requiring both commutators to be one is
consistent on sectors `01,10` and inconsistent on `00,11`: it compiles XOR,
not the desired one-sided exclusion of `11`.

This result does not refute a model-dependent mixed occurrence which places
an independently authenticated identity-label actor on the same reservoir.
It proves that such an occurrence is genuinely new information: it cannot be
obtained by dressing the active actors with a fixed Pauli packet.

For the literal first dressings the affine remainder has an exact ordinary
word form:

```text
[XU,ZV]=J S T [U,V].                                     (PDC6)
```

This is the native identity used by
`reynolds-exit-does-not-carry-pauli-gauge`; after `[U,V]=1` it exposes the
selector sign `JST`, not the pure multiplicity commutator.
