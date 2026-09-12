---
rg: 2
id: transverse-d8-two-swap-corner-unitarity-collapses-to-one-path
kind: claim
title: Corner unitarity collapses the transverse D8 two-swap sum to one path
distinct_from:
  rank-one-additive-swap-cycles-only-read-isotropy-holonomy: that uses one common rank-one partition and leaves one return path; this uses transverse Pauli partitions and computes the first genuine two-return-path sum.
  single-group-word-compression-unitary-normalizes-corner: that treats one compressed group word; this treats a coherent sum arising from two additive swap cells.
  balanced-router-pauli-holonomy-interface: that seeks a robust two-quarter return incidence; this is the exact two-dimensional swap polynomial and its unitarity fence.
---

# Corner unitarity collapses the transverse D8 two-swap sum to one path

ESTABLISHED. Work in the two-dimensional `D_8` type and choose transverse
Pauli rank-one partitions

```text
q=p_0+p_1=f_++f_-,
tau_q(p_i)=1/2,       tau_q(p_i f_j)=1/4.                (TDS1)
```

Here `(p_0,p_1)` is the Z basis and `(f_+,f_-)` the X basis. Let `A` be an
additive swap of the Z partition and `B` an additive swap of the X partition.
After identifying each packet line with one common multiplicity space, their
most general exact self-adjoint-unitary forms are

```text
A = [ 0   U^* ],
    [ U    0  ]

B = H [ 0   W^* ] H
      [ W    0  ]
  = [ S    T ],                                           (TDS2)
    [ -T  -S ]

S=(W+W^*)/2,             T=(W-W^*)/2,
```

where `U,W` are arbitrary multiplicity unitaries and `H` is the scalar
Hadamard change of basis.

The lowest-degree Z-corner entry containing more than one coherent return
path is

```text
C=p_0 B A p_0=T U=(W-W^*)U/2.                            (TDS3)
```

The two terms in `(TDS3)` are genuinely distinct before relations are added.
Since `S,T` are commuting functions of `W`,

```text
T^*T=I-S^2,
I-C^*C=U^*S^2U.                                          (TDS4)
```

Consequently `C` is unitary in the `p_0` corner if and only if

```text
S=0  iff  W^*=-W  iff  W^2=-I.                           (TDS5)
```

But under `(TDS5)`, `T=W` and

```text
B=[ 0   W ],
  [ -W  0  ],                                            (TDS6)
```

so `B` is now a single off-diagonal transport for the Z partition. The two
return paths in `(TDS3)` have become equal up to sign and the transverse
interference has disappeared. Requiring `C` to be a corner involution is
even stronger and has the same collapse.

The individual involution relations `A^2=B^2=q` constrain neither `U` nor
`W`. Standard cross relations do not create growing rigidity either. For
example `[A,B]=1` has the scalar stationary solution `U=W=iI`, while
`AB=-BA` has `U=W=I`; these are fixed Pauli packets and may be tensored with
an arbitrary contextual multiplicity model.

Thus transverse noncommuting partitions do produce the first honest
multi-return sum, but the most direct locking relation--corner
unitarity/involution--forces it back into the one-path groupoid regime. A
survivor must use a weaker polynomial which detects `S^2` at positive trace
without setting it to zero exactly, or couple at least two transverse sums so
their nonunitary deficits cannot be hidden on complementary multiplicity
sectors. Ordinary exact unitarity of one transverse corner is a no-go.
