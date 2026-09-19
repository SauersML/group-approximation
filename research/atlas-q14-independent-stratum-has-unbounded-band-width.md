---
rg: 2
id: atlas-q14-independent-stratum-has-unbounded-band-width
kind: claim
title: The independent q14 stratum contains constant-rank V4 bands of unbounded width
distinct_from:
  atlas-q14-adds-stratified-thirteenth-double-coset: that classifies complex regular involution pairs by one joint-sector integer; this exhibits modular binary transvection pairs with an unbounded similarity parameter.
  atlas-q14-exact-allows-full-coefficient-cyclicity: that puts the two marked transvections in the equal stratum and makes the chart coefficient algebra full; this constructs the opposite independent stratum where all three V4 directions have natural rank.
  atlas-multiplicity-two-joint-kernel-slice-is-empty: that exhausts one fixed-width F4-seeded packet slice; this proves q14 itself permits genuinely growing non-flag band parameters outside every fixed-width slice.
---

ESTABLISHED.  For every `m>=2`, choose an invertible
`C in GL_m(F2)` such that `I+C` is invertible.  On

```text
E=U direct_sum W direct_sum Z,
dim U=dim W=m,       dim Z=2m,                        (QBW1)
```

define

```text
N(u,w,z)=(w,0,0),
M(u,w,z)=(Cw,0,0).                                   (QBW2)
```

Then

```text
N^2=M^2=NM=MN=0,
rank N=rank M=rank(N+M)=m.                           (QBW3)
```

Thus `1+N` and `1+M` are commuting natural-transvection-type involutions on
the `4m`-dimensional repeated-natural chart space.  They lie in the fully
independent q14 stratum: all three nonidentity elements of their generated
`V4` have nilpotent rank exactly `m`.  Since `N` and `M` have the same
Jordan type `(2^m,1^(2m))`, there is a chart change `T` with

```text
M=TNT^(-1),                                          (QBW4)
```

so both extend to full conjugate repeated-natural `A8` charts and q14 is
exact.

The similarity class of `C` is intrinsic to this q14 module.  Indeed
`ker N` is contained in `ker M`, `im M` is contained in `im N`, and the
induced maps

```text
Nbar:E/ker N -> im N,
Mbar:E/ker N -> im N                                 (QBW5)
```

satisfy

```text
C=Mbar Nbar^(-1)                                     (QBW6)
```

after the canonical identification in `(QBW2)`.  An isomorphism of marked
pairs conjugates `(QBW6)`, so distinct similarity classes of `C` give
distinct independent q14 bands.

Taking `C` to be the companion matrix of an irreducible degree-`m`
polynomial other than `x` or `x+1` makes both `C` and `I+C` invertible and
gives the active coefficient algebra

```text
F2[C] ~= F_(2^m).                                    (QBW7)
```

Hence the independent q14 locus has genuinely unbounded state width even
after requiring the third V4 involution to have exactly the natural rank.
No finite equal-versus-independent type list, fixed semisimple phase audit,
or q14-only compactness theorem can cover it.  The twelve packet cubes and
collision must constrain or pay this growing field-like band parameter.

This construction does not claim packet or collision smallness.  It
identifies the exact next test family after the equal triangular slice was
closed: substitute `(QBW2)` into the thirteen post-q14 residuals and seek a
rank floor uniform over irreducible `C`, or an asymptotic family in which
those residuals become sublinear.

The irreducible-field fork is now closed by
`atlas-q14-irreducible-field-bands-pay-quarter-rank`.  The conjugator may be
chosen as `diag(C,I,I,I)`, so every residual block is a bounded-degree
Laurent polynomial in `C`.  For irreducible companions of growing degree,
one nonzero entry is invertible and forces normalized residual rank at least
`1/4`.  Thus unbounded q14 band width exists, but the primary field bands do
not evade the Atlas fillings.
