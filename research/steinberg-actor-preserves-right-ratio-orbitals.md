---
rg: 2
id: steinberg-actor-preserves-right-ratio-orbitals
kind: claim
title: The affine Steinberg actor has infinitely many right-ratio pair orbitals
distinct_from:
  finite-orbital-checksum-cannot-expose-sl3-coset-module: that uses double cosets for an arithmetic coset action; this uses the right-line fixed pointwise by a stabilizer in the affine-Leavitt linear module.
  augmentation-boundary-expands-but-not-products: that gives a partial graph product for a regular permutation module; this proves that even the much larger elementary Steinberg actor has infinitely many pair orbitals on its active linear module.
  finite-radius-active-character-packets-do-not-collapse-the-mark: that gives finite-dimensional PVM models for finite partial actor maps and locates the failure in actor loops; this gives one exact whole-actor semidirect model for every finite family of transported commutator rows, but deliberately does not impose the additive root triangles.
---

Use the affine-Leavitt notation

```text
R=L_A(k[C_aff]),
B=A R,
H=<x_ij(r):1<=i!=j<=5, r in R>,
M=B^5.                                                   (RRO1)
```

The central idempotent `A` is the identity of the active corner `B`, and
`H` acts on the column module `M` by left `R`-linear elementary matrices.
Put

```text
v=(A,0,0,0,0)^t.
```

Then the stabilizer `H_v` fixes the entire right line `vB` pointwise:

```text
h(vb)=(hv)b=vb                 (h in H_v, b in B).       (RRO2)
```

It follows that every `H`-orbit in `M times M` meets

```text
L_v={(v,vb):b in B}                                    (RRO3)
```

in at most one point.  Since `B` is infinite, the actor has infinitely many
ordered-pair orbitals.  The same conclusion holds for unordered distinct
pairs: one ordered orbital and its reverse meet `(RRO3)` in at most two
points.

Consequently, let `P` be any finite family of prototype unordered pairs in
`M\{0}`.  Join two vertices when their pair belongs to an `H`-translate of
one of the prototypes, let `K_P` be the graph product with one vertex group
`C_p=<c_m>` at every nonzero `m in M`, and form

```text
K_P rtimes H.                                            (RRO4)
```

All prototype commutators and all their actor transports hold exactly in
`(RRO4)`.  Nevertheless one can choose `b in B` for which `{v,vb}` is an
unchecked pair, and graph-product normal form gives

```text
[c_v,c_(vb)] != 1.                                      (RRO5)
```

Thus finite root-commutator prototypes plus Steinberg actor conjugacy do not
expose even the whole commutation table of the active module.  Property
`(T)` of `H` is irrelevant at zero defect, and increasing the matrix rank
from five does not remove the right-line invariant.

This does not refute the full affine-Leavitt decoder: `(RRO4)` omits the
same-root additive triangles `c_m c_n=c_(m+n)` and the mixed Steinberg
multiplication triangles which couple different coefficient addresses.
It proves that those nonlinear triangles, rather than high transitivity or
commutator transport, must perform the global exposure.  Any positive proof
must give a uniform normalized-HS estimate charging their moving loop
failures.

