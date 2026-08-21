---
rg: 2
id: two-pauli-quarter-carriers-have-fixed-reflection-holonomy
kind: claim
title: The two canonical Pauli quarter carriers generate an exact positive-density D8 holonomy packet
artifacts:
  - experiments/atlas_transported_corner_overlap.py
  - experiments/atlas-transported-corner-overlap.json
distinct_from:
  transported-coefficient-corners-share-flat-quarter-carrier: that constructs the capacity-generated common corner and its character fingerprints; this computes its noncommutative angle against the separate branch-transfer carrier.
  fixed-holonomy-on-overlap-pays-relator-energy: that turns word-level reflection holonomy into a relator-energy floor; this supplies the exact Hecke/projection holonomy but does not yet expose both reflections as legal group words.
---

Let `F` be the trace-quarter common projection of the two transported
coefficient corners, and let `G` be the separate trace-quarter comb-transported
carrier of the Pauli branch-transfer packet.  Exact rational prefix
arithmetic gives

```text
tau(F)=tau(G)=1/4,
tau(FG)=1/16,
tau(FGFG)=3/64.                                      (QFH1)
```

Hence

```text
tau(FG)-tau(FGFG)=1/64,                              (QFH2)
```

so `F` and `G` do not commute.  For the projection reflections

```text
R_F=2F-1,       R_G=2G-1,
```

the two-projection identity gives

```text
||R_F R_G R_F R_G-1||_2^2
  =32(tau(FG)-tau(FGFG))
  =1/2.                                              (QFH3)
```

This is a fixed normalized-HS holonomy already present in the exact atlas
packet.  It is stronger than mere non-identification of the carriers and is
immune to spectator amplification.

The holonomy is not merely metric.  Exact reduction also gives

```text
(R_F R_G)^3 != 1,
(R_F R_G)^4 = 1.                                     (QFH4)
```

Since `R_F,R_G` are involutions and do not commute, they generate a literal
dihedral group `D_8`.  Its central commutator is

```text
K=[R_F,R_G]=(R_F R_G)^2,
K^2=1,
tau(K)=3/4.                                          (QFH5)
```

Therefore the negative central cut

```text
H=(1-K)/2
```

has trace exactly `1/8`.  On `H`, the two reflections anticommute:

```text
H R_F R_G = - H R_G R_F.                             (QFH6)
```

Thus the overlap itself manufactures a fresh exact Pauli pair on a canonical
positive-density corner.  No spectral truncation or condition-number
estimate is needed.

It is not yet a group-presentation contradiction.  The reflections are
Hecke/projection polynomials, not automatically words in the original unitary
generators, and no defining relation currently requires them to commute.
The narrowed compiler target is therefore finite and explicit: implement
this `D_8` as a legal derived packet (the gauge-doubled router construction is
designed for exactly this issue), then make the mixed rank-five return demand
trivial holonomy or feed its trace-`1/8` Pauli corner into the next proper
compressor cell.  If that implementation has dimension-independent decoding
loss below `1/2`, `(QFH3)` supplies the fixed energy floor required by the
nonhyperlinearity route.
