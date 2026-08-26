---
rg: 2
id: sublinear-julia-seam-collapses-the-fold-kernel-tracially
kind: claim
title: A sublinear-rank Julia seam makes the whole fold kernel tracially null
distinct_from:
  weak-mf-embedding-not-reusable: that dilutes a general norm model by adding identity blocks; this gives an intrinsic rank bound for every fold-kernel word in one globally conjugate presentation-double model.
  finite-cross-word-family-fits-one-hall-reflection: that constructs a rank-one Hall model for canonical length-two cross words; this treats arbitrary alternating words and any sublinear-rank Julia conjugator.
  corona-representations-have-an-ideal-valued-support-length: that assigns an abstract ideal support to every corona word; this computes a uniform principal-rank upper bound for the entire fold kernel from one Julia seam.
---

**ESTABLISHED JULIA RANK FIREWALL.** Let `P=F *_K F`, let
`fold:P->F` identify its two vertex copies, and let

```text
sigma:F->U(d),                  V in U(d),
rho(i_0(f))=sigma(f),           rho(i_1(f))=V^*sigma(f)V.   (SJS1)
```

Put `r=rank(V-1)`. If `w` is represented by `L` vertex syllables, of which
`m` lie in the second copy, then

```text
rank(rho(w)-sigma(fold(w))) <= 2m r <= 2Lr.            (SJS2)
```

In particular, for every `w in ker(fold)`,

```text
||rho(w)-1||_(2,d)^2 <= 8L r/d,
|tr_d(rho(w))-1|     <= 4L r/d.                        (SJS3)
```

Consequently, if `r_n/d_n->0`, then **every fixed word in the whole fold
kernel**, not only the canonical length-two cross words, becomes the identity
in the tracial ultraproduct. It may remain separated in operator norm.

There is a matching statement on the adjoint seed used by the
presentation-double retention program. For every `f in F`,

```text
||Ad(sigma)(f)V-V||_(2,d) <= 2 sqrt(2r/d).             (SJS4)
```

Thus the line `C V` is uniformly almost `F`-reducing when the Julia seam has
sublinear rank. If `V` is also pointwise quasicentral for `sigma(K)`, that
line has `(IR1)` and `(IR2)`, but `(SJS4)` forces `(IR3)` to vanish. The
operator wall carried by the seam supplies no trace-visible quotient motion.

This does not show that Shulman's faithful norm-corona coordinates can be
chosen with `rank(V_n-1)=o(d_n)`. It proves the exact missing structural
input: longer alternating words by themselves cannot promote the wall.
Positive-rank intertwiner retention must either prove that every admissible
Julia seam spreads to macroscopic relative rank, or extract a positive
kernel-energy band whose surviving motion is not confined to the seam's
principal rank ideal.

DERIVATION
sublinear-julia-seam-rank-proof
