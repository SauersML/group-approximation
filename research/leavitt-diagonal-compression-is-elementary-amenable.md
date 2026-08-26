---
rg: 2
id: leavitt-diagonal-compression-is-elementary-amenable
kind: claim
title: The diagonal Leavitt elementary subgroup with one compressor is elementary amenable and contains the mark
artifacts:
  - research/leavitt-diagonal-compression-amenability-proof.md
distinct_from:
  amenable-multi-compressors-have-a-joint-hs-telescope: that is a Kun--Thom Hilbert--Schmidt statement about arithmetic actors; this identifies a literal locally finite subgroup of the binary-Leavitt manuscript group on which one manuscript compressor acts by self-similarity and the mark remains MF-visible.
  norm-corona-locally-finite-compression-countermodel: that constructs the compression phenomenon abstractly in a tensor norm corona; this locates it inside the literal Leavitt elementary group and pins the manuscript mark in the amenable subgroup.
  finite-positive-root-fragments-have-marked-regular-models: that gives exact finite models for each finite positive-root window; this gives one infinite amenable subgroup containing both the mark and a compressor.
---

Let `R=L_(F_2)(1,2)`, with

```text
p=s_0t_0,                    q=s_1t_1,
L=EL_3(R)<=EL_12(R),         z=x_13(q).
```

The manuscript compressor `tau in EL_12(R)` implements on `L` the
multiplicative embedding

```text
Psi(A)=qI_3+s_0At_0.                                  (DLC1)
```

Let `tau'` be its image under the binary branch-exchange automorphism; it
implements `Psi'(A)=pI_3+s_1At_1`.

Let `D<=R` be the additive span of the cylinder idempotents `s_wt_w`, and
put `Lambda=EL_3(D)`.  Then:

1. `D` is the ring of locally constant `F_2`-valued functions on the
   binary Cantor set and
   `D=union_k D_k`, `D_k=directSum_(|w|=k) F_2 s_wt_w`;
2. `Lambda=union_k Lambda_k`, with
   `Lambda_k=EL_3(D_k)=GL_3(F_2)^(2^k)`, so `Lambda` is countable and
   locally finite;
3. `Psi(Lambda),Psi'(Lambda)<=Lambda`, the two images commute, and
   `Lambda_(k+1)=Psi(Lambda_k) x Psi'(Lambda_k)`;
4. the manuscript mark `z=x_13(q)` belongs to `Lambda_1`;
5. `A_0=<Lambda,tau>` and, symmetrically, `<Lambda,tau'>` are elementary
   amenable.  Consequently they are operator-MF and have trivial MF
   radical, so the mark is MF-visible in either one-compressor subgroup.

Hence no proof that the mark lies in the MF radical of the full Leavitt
group can use only diagonal-root relations and one compressor.  Every such
relation already holds in the amenable group `A_0`, where a norm-corona
representation separates `z`.  A load-bearing Property-`(T)`-free row must
use a non-diagonal root occurrence or both complementary compressors.

The full two-compressor group `<Lambda,tau,tau'>` is not decided here.
Likewise the compatible character tower on the locally finite groups
`Lambda_k` admits both trivial and regular profiles, so diagonal
self-similarity alone does not select the manuscript's desired profile.

No Property `(T)`, stability theorem, or literature input is used.

DERIVATION
leavitt-diagonal-compression-amenability-proof
