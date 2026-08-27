---
rg: 2
id: boolean-violation-is-one-raw-radical-qubit-drop
kind: claim
title: Every Boolean violation is one rank drop with two fixed raw radical words
artifacts:
  - experiments/boolean_predicate_radical_cycle.py
distinct_from:
  boolean-predicate-is-one-rank-jump: that uses an invertible Schur block and makes a violation add one spin qubit; this makes a violation remove one spin qubit and exposes its resulting radical by fixed group words.
  raw-schur-generator-is-not-child-center: that shows the Schur compiler's raw last generator does not label the child simples; this alternative compiler makes both child labels literal products of packet generators on every forbidden atom.
  finite-predicate-signed-permutation-sector: that exposes predicate support in a chosen representation block; this computes the complete sector algebra of a class-two group packet.
---

Let `f:{0,1}^k->{0,1}` and let `F=f^(-1)(1)`.  There is an effectively
constructible affine square matrix `C_f(x)` of size

```text
N=k|F|                                                        (BRD1)
```

when `k>0`, with the following properties:

```text
rank C_f(x)=N-f(x),                                           (BRD2)
```

and for every `a in F` there are fixed zero-one vectors `u_a,v_a` such that
at `x=a`

```text
u_a^T C_f(a)=0,             C_f(a)v_a=0.                      (BRD3)
```

Both vectors are supported on the block belonging to `a` and are all one on
that block.  Off the `a`-sector that block is invertible.

Symmetrize the matrix:

```text
A_f(x)=[[0,C_f(x)],[C_f(x)^T,0]].                             (BRD4)
```

Then `A_f` is an affine alternating form of rank

```text
rank A_f(x)=2N-2f(x).                                         (BRD5)
```

Use it as the commutator form of a finite class-two packet with row
generators `p_i`, column generators `q_i`, selectors, and marked sign `J`.
On a satisfying selector sector its marked algebra is one full block

```text
M_(2^N)(C).                                                    (BRD6)
```

On the forbidden sector `a`, it is

```text
direct_sum_4 M_(2^(N-1))(C).                                  (BRD7)
```

The four simples in `(BRD7)` are labeled by the signs of the two literal
group words

```text
P_a=product_(i in supp u_a) p_i,
Q_a=product_(j in supp v_a) q_j.                              (BRD8)
```

Indeed `P_a,Q_a` commute with the entire packet on the `a`-sector and span
its two-dimensional radical.  Thus violation Hilbert mass `q` contributes
twice as many irreducible packet copies per baseline dimension as satisfying
mass `q`, while its four branches are exposed by fixed raw words rather than
by a selector-controlled group-algebra coefficient.

For AND with forbidden assignment `(1,1)`, the unsymmetrized block is simply

```text
C(x,y)=[[1,x],[y,1]],                                         (BRD9)
```

and the hot radical words are `p_0p_1` and `q_0q_1`.
