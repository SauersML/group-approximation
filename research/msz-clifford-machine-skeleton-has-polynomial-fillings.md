---
rg: 2
id: msz-clifford-machine-skeleton-has-polynomial-fillings
kind: claim
title: The MSZ Clifford machine skeleton embeds with polynomial fillings
artifacts:
  - research/artifacts/mehta-slofstra-zhao-positivity-ingestion-2026-08-20.md
distinct_from:
  quantitative-higman-embedding-with-dehn-control: that is a general embedding theorem; this is a concrete machine group to which the theorem applies and records its addressed Clifford commutator schedule.
  uniform-halting-pauli-word-oracle: that asks for constant-average soundness and a post-halting Pauli question sampler; this gives polynomial fillings for one preterminal Clifford tape and no average-query oracle.
---

For every recursively enumerable set `L`, Mehta--Slofstra--Zhao construct a
six-generated group `G_L=<J,S,T,W,X,Z>` with central involution `J` and
addressed involutions

```text
X_(m,i)=S^i W^m X W^(-m) S^(-i),
Z_(m,i)=T^i W^m Z W^(-m) T^(-i).                                (MCS1)
```

If `h(m)` is the halting time, with `infinity` for nonhalting, then the local
cell has

```text
[X_(m,i),Z_(m,i)] = J   when i+1 != 0 mod h(m)+1,
[X_(m,i),Z_(m,i)] = 1   at the unique terminal residue.           (MCS2)
```

Different sites at fixed `m` commute in the prescribed Pauli coordinates.
The construction is an amalgam of central products of `D_4` and
`C_2^3` cells followed by three HNN shifts.  Britton reduction and the
explicit central-product normal form solve the word problem of `G_L` in
deterministic polynomial time.

There is therefore an embedding into a finitely presented group

```text
G_L -> H_L=<X_H|R_H>
```

whose generators may all be chosen involutions and a polynomial `d_L` such
that every trivial `G_L` word `w` has an `R_H` filling

```text
w = product_(j=1)^r z_j r_j z_j^(-1),
r <= d_L(|w|),             |z_j| <= d_L(|w|).                    (MCS3)
```

This supplies an exact, finitely presented, polynomial-cost computation tape.
Its later projection-doubling gate is nevertheless additive in the group
algebra.  Thus `(MCS1)--(MCS3)` solve addressing and filling cost, but not the
normalized-HS groupification boundary.
