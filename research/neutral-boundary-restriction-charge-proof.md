---
rg: 2
id: neutral-boundary-restriction-charge-proof
kind: route
title: Subtract the extendible boundary in the representation group
target: neutral-boundary-compressions-have-zero-restriction-charge
requires:
  - three-way-cell-semigroups-have-conductor-but-unbounded-charge
  - positive-fixed-corner-cubic-energy-charges-deleted-rank
  - bs14-trivial-boundary-inversion-forces-r-fixed-source
---

Restriction of `(NRC2)` to `B` gives the exact equality in the positive
representation monoid

```text
res[pi]=r[tau]+[beta].                                  (NRP1)
```

Because `tau` extends to `Gamma`, its class belongs to the restriction
image.  Rearranging `(NRP1)` in its Grothendieck group gives `(NRC3)`.
No irreducible decomposition, scalar-packet authentication, or finiteness of
the restriction image is used.

In the BS14 positive-corner setup, the block equations in
`bs14-trivial-boundary-inversion-forces-r-fixed-source` force the neutral
boundary core to have

```text
R_Q=S_Q=1.                                             (NRP2)
```

It is therefore `r` copies of the restriction of the trivial Iwahori
representation, and `(NRC3)` applies.

Now assume the compression `C=QXQ` is positive with spectrum in `(0,a_0]`.
The exact identity from
`positive-fixed-corner-cubic-energy-charges-deleted-rank` is

```text
E=Tr_Q f(C) >= f(a_0)r.                               (NRP3)
```

Adjoining the original boundary space `QH` and restoring the original exact
endpoint representation uses exactly `r` dimensions.  If `A=PXP` and
`X_0=sgn(A)`, then

```text
||X_0-A||_F^2<=r,                 ||QXP||_F^2<=r.      (NRP4)
```

Thus, under the natural inclusion of `PH` into `H`, the discrepancy between
the compressed polar involution and the exact endpoint generator is
`O(sqrt(r))` in Frobenius norm, while the exact core generators agree on
`PH`.  Divide by the enlarged dimension and use `(NRP3)` to obtain `(NRC4)`
and the stated normalized displacement.

This direction deliberately starts with the exact endpoint.  Reversing it
would require constructing `Q`, its trivial core action, and the full
involution from the two compressed residuals.  The representation-group
identity `(NRP1)` cannot manufacture those operator blocks, so it does not
assume the open reverse-dilation theorem.
