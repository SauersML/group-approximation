---
rg: 2
id: binary-jacobson-monomial-symbol-preimage-is-marked-mf
kind: claim
title: The monomial Laurent-symbol preimage has its regular MF character, and one raw root is the generation threshold
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

Then `K` is countable amenable and its regular character is an MF character.
Explicitly, there are operator-norm asymptotic unitary representations
`sigma_n:K->U(d_n)` such that

```text
tr_(d_n)(sigma_n(g))->delta_1(g)                       (JMP3a)
```

for every `g in K`.  In particular `K` is operator-MF and retains the head
root:

```text
z_Q in K,                    z_Q!=1.                  (JMP3)
```

Since `z_Q` is a nonidentity involution, operator-norm involution rounding
may be applied without changing `(JMP3a)`.  Its negative spectral projection
then has normalized rank tending to `1/2` and operator norm one.  Thus this
is a positive-density regular-profile head model, not merely a sparse
norm-corona witness.

Consequently the full preimage of `K` under `St_5(J)->E` has a
norm-matrix-corona representation in which `x_13(Q)` is nontrivial.  Thus no
finite ordinary-word packet contained in this subgroup can authenticate a
same-square Toeplitz reservoir on every surviving head coordinate.  More
strongly, no such packet plus regular-character trace data can do so: the
canonical regular profile itself occurs in the models `(JMP3a)`.

This firewall reaches an exact generation threshold.  For every `i!=j`,

```text
<K,x_ij(1)>=E.                                             (JMP4)
```

Indeed balanced monomial torus conjugations produce every `x_ij(z^n)` from
the constant symbol root.  Weyl
permutations produce every root position, and root additivity produces every
Laurent coefficient.  Since `K` already contains the complete finitary
kernel of `(JMP1)`, this generates all of `E`.

The previously recorded seams `x_ij(S)` and `x_ij(T)` are equivalent:
their symbols are Laurent conjugates of `x_ij(1)`, and the discrepancy
between any chosen lifts lies in the finitary kernel already contained in
`K`.

Hence the relations missing from the marked-MF subsystem are not another
head permutation, balanced shift, Weyl transport, or monomial holonomy.  The
first possible square-authentication seam is precisely the interaction of
one constant raw root having a **nonmonomial elementary symbol** with the
monomial-symbol preimage.  Statement `(JMP4)` makes no assertion that the
resulting full group `E` is MF.

DERIVATION
binary-jacobson-monomial-symbol-preimage-proof
