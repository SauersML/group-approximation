---
rg: 2
id: fixed-parity-faces-exactify-with-loewner-row-square-control
kind: claim
title: Fixed parity faces exactify with Loewner row-square control
distinct_from:
  whole-face-sign-rounding-does-not-inherit-gap-contraction: that signs one whole-face pinching and gives Hilbert--Schmidt energy bounds but no operator-order correction ledger; this constructs an exact commuting parity face with a Loewner bound.
  gapped-face-pinchings-give-same-hilbert-code-pvm-rounding: that uses a global face-Hamiltonian gap; this is a fixed-width local construction requiring no global gap or character decomposition.
  sparse-face-row-square-survives-intrinsic-green-step: that needs a row-square-preserving correction after every damped intrinsic step; this supplies that correction.
---

ESTABLISHED.  Fix `q`.  There is a constant `C_q` and a finite set
`W_q` of words of length bounded in terms of `q` with the following
property.  Let `X_1,...,X_m`, `m<=q`, be selfadjoint contractions and let
`epsilon in {+1,-1}`.  Define the local residual square

```text
 H_face=sum_i(I-X_i^2)
       +sum_(i<j)[X_i,X_j]^*[X_i,X_j]
       +(X_1...X_m-epsilon I)^*(X_1...X_m-epsilon I),  (LFE1)
```

and let `H_face^sym` be the sum of the finitely many left/right word
conjugates of the summands in `(LFE1)` indexed by `W_q`.  Then there are
commuting reflections `S_1,...,S_m` with product `epsilon I` such that

```text
 sum_i(X_i-S_i)^2 <=C_q H_face^sym.                    (LFE2)
```

All inequalities are in Loewner order.  In particular, on a reducing block
where `H_face^sym<=bI`, the entire local correction has operator row square
at most `C_qbI`.

The construction is explicit.  First sign each contraction.  Install the
reflections sequentially.  If `A_1,...,A_r` are already commuting, average
the next reflection `B` over their finite abelian group,

```text
 E(B)=|G|^(-1)sum_(g in G)gBg,
```

and replace it by `sgn(E(B))`.  After the first `m-1` coordinates commute,
replace the last one by `epsilon product_(i<m)S_i`.  The constants are
uniform because `m<=q`.

For a bounded-width repeated face system, apply the construction separately
to each occurrence face and average `(LFE2)` with the normalized face
weights.  Bounded occurrence gives

```text
 sum_(c,i)w_(c,i)(X_(c,i)-S_(c,i))^2
 <=C_q H_sparse^sym,                                   (LFE3)
```

where `H_sparse^sym` is one fixed finite symmetrization of the raw parity,
commutator, and involution square function.  Including this finite
symmetrization in the common outlier square changes all normalized traces
and covariance constants only by `C_q`.  Thus exact local face copies can
be produced inside the retained reducing block without leaving its
operator row-square basin.
