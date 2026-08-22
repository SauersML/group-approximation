---
rg: 2
id: sparse-generator-column-sampling-has-bilinear-kernel
kind: claim
title: Sparse generator-column sampling cannot spectrally recover the full Weyl table
distinct_from:
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that proves uniform global exactification from the complete product of the two generator-column measures; this proves no bounded-degree sub-sampler can imply its full-product defect estimate by a spectral comparison.
  bounded-neighbor-pauli-needs-growing-equality-components: that builds constant-dimensional models for arbitrary sparse pairwise signed graphs without linearity; this keeps both exact additive group laws and isolates the remaining affine minimum-rank obstruction.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that degree-reduces repeated occurrences while retaining every logical test; this asks whether the logical generator-column cross table itself can be sparsified and proves that ordinary sampler expansion is insufficient.
---

Let `H=F_2^n`.  Let `a_i in H`, `1<=i<=K`, and `b_j in H`,
`1<=j<=K'`, be the two spanning generator-column multisets used in the de la
Salle Pauli test, with inverse spectral-gap constants at most `c,c'`.  Let

```text
E subset {1,...,K} times {1,...,K'}
```

be any sampled pair set with `|E|<n^2`; in particular this holds for every
fixed-degree bipartite sampler once `K,K'=Theta(n)`.

There is a nonzero bilinear form `M in M_n(F_2)` such that

```text
a_i^T M b_j=0                       ((i,j) in E).       (SGB1)
```

Put `B=I+M`.  There is an exact Weyl representation on dimension

```text
2^rank(B)                                                    (SGB2)
```

whose X and Z maps obey both exact additive laws and whose sampled cross
relations have the ideal signs

```text
X(a_i)Z(b_j)=(-1)^(a_i.b_j)Z(b_j)X(a_i)   ((i,j) in E). (SGB3)
```

Nevertheless its full-product ideal Weyl defect is bounded below uniformly:

```text
E_(i,j)||X(a_i)Z(b_j)
 -(-1)^(a_i.b_j)Z(b_j)X(a_i)||_2^2 >= 1/(c c').         (SGB4)
```

Thus no inequality of the form

```text
full generator-column Weyl energy
 <= C times sampled-edge Weyl energy                           (SGB5)
```

can hold for a bounded-degree graph, regardless of its ordinary spectral gap
or girth.  The right side can be zero while the left side is constant.

This does not by itself give a constant-dimensional escape, because
`rank(I+M)` may still grow.  It identifies the exact surviving algebraic
criterion.  Define

```text
r(E)=min { rank(B):
            a_i^T B b_j=a_i.b_j for every (i,j) in E }.        (SGB6)
```

The scalar-Weyl exact strategies for the sampled test have minimum dimension
`2^r(E)`.  Therefore a sparse robust dimension witness must construct
bounded-incidence sets `E_n` for which `r(E_n)->infinity`, and then prove an
amplification-stable approximate minimum-rank theorem.  Neither bipartite
expansion nor a derandomized-product estimate supplies this: `(SGB1)--(SGB5)`
exclude the required full-table transfer.

Consequently the sparse alternative in
`colored-cayley-pauli-incidence-separation` is now a concrete rank-metric
local-testing problem, rather than a graph-sampler problem.  It may still be
possible, but it must force growing completion rank without first recovering
all `n^2` Weyl signs.

Growing exact rank is indeed possible despite the kernel:
`degree-one-generator-columns-have-sqrt-minrank-but-no-gap` constructs a
matching sampler with `r(E)=Theta(sqrt(n))` by repeating basis columns and
using additivity to force a triangular identity block.  That example also
shows why exact rank is not the robust theorem needed here: bounded-rank
models approximate its sampled syndrome with arbitrarily small relative
error.
