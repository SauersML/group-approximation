---
rg: 2
id: steinberg-fox-rows-generate-defect-zero-block
kind: claim
title: The two Fox rows generate the unit left ideal in every Steinberg block
---

For every odd prime `p`, in the matrix block

```text
A_p=F_p[SL_3(F_p)]/Ann(St_p),
```

the images `x,y` of the rows in `(SFI2)` satisfy

```text
A_p x+A_p y=A_p.                                      (SBUG1)
```

Equivalently, there are block endomorphisms `a_p,b_p` with
`a_p x+b_p y=1`.  By `steinberg-fox-injectivity-is-block-bezout`, this is
the exact coordinate-free payload needed to close the Steinberg flag map.
The open issue is a proof uniform in `p`, not the existence of a certificate
after injectivity is already known.

## Attempts

The spherical/Iwahori Hecke corner sees only the `B`-fixed line and cannot
by itself certify the unit ideal in the full `p^3`-dimensional block.  A
successful argument must control the non-equivariant root-coordinate data,
for example through PBW triangularity, the explicit chord recurrence, or a
direct block identity.
