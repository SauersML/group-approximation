---
rg: 2
id: bs14-native-cells-cross-every-length-cutoff
kind: claim
title: Exact BS14-Iwahori cells cross every finite orbit-length cutoff
distinct_from:
  even-weil-fixed-line-compression: that constructs the one-line compression and its near-extension; this extracts the obstruction to a short/long native-cell factorization.
  bs14-long-packet-monodromy-reset-creates-fixed-sources: that resets return phase within each packet; this shows that phase-one packets still couple across arbitrarily separated orbit lengths.
  fixed-level-bs14-compatible-basin: that records the quantitative basin problem after global finite-period preconditioning; this rules out repairing only the short side of a length cutoff.
---

For every `M` there is an exact finite-dimensional Iwahori tuple whose exact
BS core decomposes as

```text
H=QH (+) PH,              dim(QH)=1,                 (NLC1)
```

where `QH` is the trivial length-one packet, every nonzero fourth-power
spectral orbit in `PH` has one common length `m>M`, all return monodromies
are one, and the exact involution `X` necessarily has

```text
PXQ !=0.                                                (NLC2)
```

Thus the native joint-cell support does not split into independent
`m<=M` and `m>M` semigroups, even after the long-packet monodromy reset.

Take the full even-Weil representation for a prime `p=1 mod 4`.  Its BS
restriction is the fixed line `C delta_0` plus the nonzero Schrödinger
coordinates.  The fourth-power permutation has orbit length

```text
m=ord_p(4),                                            (NLC3)
```

and, being an honest permutation cycle, has return phase one.  These
lengths are unbounded on primes `p=1 mod 4`: otherwise every such prime
would divide the fixed finite integer

```text
product_(ell=1)^M (4^ell-1),                           (NLC4)
```

contradicting the infinitude of primes congruent to one modulo four.

The coupling `(NLC2)` is not a choice of gauge.  The compression theorem
gives exactly

```text
||PX delta_0||^2=1-1/p.                               (NLC5)
```

Alternatively, if `X` preserved `PH`, all five exact Iwahori relations
would restrict to `PH`, contradicting the proved nonextension of the
dimension `(p-1)/2` compressed core.  Hence an exact cell can pair one
short source with arbitrarily long exit data at order-one unnormalized
coupling.

This refutes a naive synthesis in which one computes the native semigroup
for each `m<=M`, repairs its active mass, and treats `m>M` independently.
The active rank is still only one in this example and is correctly paid by
the cubic energy, but the **cell realizing that payment straddles the
cutoff**.  A valid staircase must retain cross-threshold source/exit cells,
or move the cutoff only after a global cell decomposition has been
authenticated.  Packetwise monodromy reset and passive deletion alone do
not build the exact `X`.

