---
rg: 2
id: binary-jacobson-monomial-symbol-preimage-is-marked-mf
kind: claim
title: The full monomial Laurent-symbol preimage is marked MF, and one raw Laurent root is exactly the generation threshold
artifacts:
  - research/binary-jacobson-monomial-symbol-preimage-proof.md
distinct_from:
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that retains the finitary head under one cyclic Whitehead translation; this retains the preimage of the entire determinant-one monomial Laurent subgroup, including all balanced ray translations and Weyl permutations.
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that shows every finite quotient of the full elementary group kills the head root; this constructs a faithful norm-corona model only for a proper amenable subgroup and identifies the first symbol generator which leaves it.
  leavitt-first-offdiagonal-core-is-marked-non-lef: that uses one raw inverse-prefix root to reconstruct the full Jacobson elementary group and obtains a finite-table obstruction; this proves that everything before that raw nonmonomial symbol root remains operator-MF.
---

Let

```text
J=F_2<S,T | TS=1>,             Q=1-ST,
E=EL_5(J),                     z_Q=x_13(Q),
A=F_2[z,z^(-1)].
```

Write

```text
mu:E -> EL_5(A)                                      (JMP1)
```

for the symbol map, and let `M` be the determinant-one monomial Laurent
subgroup: its matrices have one nonzero entry in every row and column, every
nonzero entry is a power of `z`, and the total exponent is zero.  Put

```text
K=mu^(-1)(M).                                        (JMP2)
```

Then `K` is countable amenable and operator-MF, and it retains the head root:

```text
z_Q in K,                    z_Q!=1.                  (JMP3)
```

Consequently the full preimage of `K` under `St_5(J)->E` has a
norm-matrix-corona representation in which `x_13(Q)` is nontrivial.  Thus no
finite ordinary-word packet contained in this subgroup can authenticate a
same-square Toeplitz reservoir on every surviving head coordinate.

This firewall reaches an exact generation threshold.  For every `i!=j`,

```text
<K,x_ij(S)>=E,                 <K,x_ij(T)>=E.          (JMP4)
```

Indeed the symbol of the added root is `x_ij(z)` or `x_ij(z^(-1))`.
Balanced monomial torus conjugations produce every `x_ij(z^n)`, Weyl
permutations produce every root position, and root additivity produces every
Laurent coefficient.  Since `K` already contains the complete finitary
kernel of `(JMP1)`, this generates all of `E`.

Hence the relations missing from the marked-MF subsystem are not another
head permutation, balanced shift, Weyl transport, or monomial holonomy.  The
first possible square-authentication seam is precisely the interaction of
one raw root having a **nonmonomial Laurent elementary symbol** with the
monomial-symbol preimage.  Statement `(JMP4)` makes no assertion that the
resulting full group `E` is MF.

DERIVATION
binary-jacobson-monomial-symbol-preimage-proof
