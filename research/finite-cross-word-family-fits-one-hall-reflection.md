---
rg: 2
id: finite-cross-word-family-fits-one-hall-reflection
kind: claim
title: Any finite family of canonical cross words fits one trace-null Hall reflection
distinct_from:
  hall-reflection-realizes-rank-one-restriction-instability: that treats one fixed quotient word along an exhaustion; this simultaneously separates any prescribed finite family and permits arbitrarily large coset dimension without identity padding.
  weak-mf-embedding-not-reusable: that dilutes an arbitrary norm model by a common identity block; this gives an explicit globally conjugate two-vertex model whose separating unitary differs from the identity in rank one.
  shulman-presentation-double-witnesses-have-adjoint-normal-form: that supplies simultaneous faithfulness for every word of the full double; this shows that all canonical length-two cross words, even jointly on finite windows, impose no trace-spreading constraint.
---

**ESTABLISHED MULTIWORD CALIBRATION.** Let `Q=F/K` be infinite and simple,
let `R subset K` be finite, and let

```text
E={f_1,...,f_m} subset F\K.                            (HMF1)
```

For every `N` there are an exact permutation representation
`sigma:F->U(d)` with `d>=N` and a rank-one reflection `V=1-2p` such that

```text
[sigma(k),V]=0                         (k in R),
||[sigma(f_j),V]||_op=2                (1<=j<=m),       (HMF2)
||Ad(sigma)(f_j)V-V||_(2,d)=sqrt(8/d) (1<=j<=m).       (HMF3)
```

Consequently, with `u=V sigma V` and `v=sigma`, the two exact vertex
representations agree on all of `R`, while every canonical cross word

```text
i_0(f_j)i_1(f_j)^(-1)                                  (HMF4)
```

has operator-norm gap `2`. All these gaps are nevertheless supported in the
union of the basepoint line and its `m` images, of rank at most `m+1`; their
normalized tracial mass can be made arbitrarily small by increasing `d`.

The proof uses Hall separability twice. First choose a finite-index subgroup
`L_0<=F` containing `H=<R>` and excluding every `f_j`. Since `H` has infinite
index in `F`, Hall's free-factor form can be used with

```text
L_0=H*J,                         J!=1.                 (HMF5)
```

Pass to finite-index subgroups `L<=L_0` containing `H` with arbitrarily
large index, obtained by killing `H` and sending a nontrivial free quotient
of `J` to larger finite groups. Every such `L` still excludes all `f_j`.
The coset representation on `F/L` and its basepoint reflection give
`(HMF2)--(HMF3)` exactly.

Thus passing from one cross word to any **fixed finite family** does not force
the Shulman operator-norm defect to spread over positive normalized rank.
Any positive retention theorem must use longer alternating words in a way
that couples their defect supports, or a single simultaneous all-word
property not inherited from finite-window norm faithfulness. Merely enlarging
the finite list of canonical cross words remains compatible with this
vanishing-rank model.

The statement diagonalizes. Choose exhaustions

```text
R_n increase K,                   E_n increase F\K,
```

and in the construction demand

```text
d_n>=n(|E_n|+1).                                      (HMF6)
```

Then `u_n,v_n` agree eventually on every element of `K`, every fixed
canonical cross word has operator gap `2` eventually, and the joint support
of **all** cross-word defects indexed by `E_n` has relative rank at most

```text
(|E_n|+1)/d_n<=1/n.                                   (HMF7)
```

So even simultaneous operator visibility of every length-two cross word in
one diagonal sequence is compatible with aggregate trace-zero support. The
missing coupling must come from genuinely alternating words (or equivalent
full-amalgam structure), not from diagonalizing the canonical cross-word
family more carefully.

DERIVATION
finite-cross-word-hall-reflection-proof
