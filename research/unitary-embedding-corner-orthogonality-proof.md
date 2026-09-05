---
rg: 2
id: unitary-embedding-corner-orthogonality-proof
kind: route
title: Count the parity sectors of the conjugate tensor cube on three labels
target: unitary-embedding-does-not-preserve-corner-orthogonality
requires: []
artifacts:
  - experiments/tensor_conjugate_embedding_corner_defect.py
---

**The map.**  Tensor products and complex conjugation preserve
multiplication, so `Phi(uv)=Phi(u)Phi(v)`; they preserve adjoints as well,
so the image is unitary.  For a scalar,

```text
Phi(zI)=z^2 bar(z) I=zI.                                (TCP1)
```

For injectivity, diagonalize `u` with eigenvalues `lambda_1,lambda_2,
lambda_3` and orthonormal eigenvectors `v_i`.  For each `i,j` the tensor
`v_i tensor v_j tensor bar(v_j)` is an eigenvector of `Phi(u)` with
eigenvalue

```text
lambda_i lambda_j bar(lambda_j)=lambda_i.               (TCP2)
```

So `Phi(u)=I` forces every `lambda_i=1`, hence `u=I`.  For every projection
`p` the reflection `r_p=I-2p` is a unitary involution, so `Phi(r_p)` is one
too and `(TCE2)` is indeed a projection.

**The counts.**  In the tensor basis `e_i tensor e_j tensor bar(e_k)` the
eigenvalue of `Phi(r_p)` is negative exactly when the number of occurrences
of label `1` among `i,j,k` is odd, and that of `Phi(r_q)` exactly when the
number of occurrences of label `2` is odd.  The number of triples with an
odd number of a fixed label is

```text
3.2^2+1=13,                                             (TCP3)
```

giving `rank F(p)=rank F(q)=13`.  Both parities are odd precisely when the
three labels are a permutation of `1,2,3`, which is six basis vectors, so
`rank F(p)F(q)=6` and `tr_27=2/9`; the product of two commuting nonzero
projections with a common vector has norm `1`.

Since `pq=0`, the source reflections satisfy `r_(p+q)=r_p r_q`.  Their
images commute, and expanding the product gives `(TCE4)`; the sign pattern
of `F(p+q)` is the parity of the number of labels in `{1,2}`, which is the
exclusive or of the two indicators, so `rank F(p+q)=14` and the additive
error is `2F(p)F(q)`.

**The exact leaked mass.**  The three-hot atom on distinct `i,j,k` has range
the orthogonal sum of the six tensor products `P_a tensor P_b tensor bar(P_c)`
with `(a,b,c)` a permutation of `(i,j,k)`, each of normalized rank
`alpha_i alpha_j alpha_k`; that is `(TCE5)`.  Expanding
`(sum_i alpha_i)^3=1` and separating triples with all indices equal, exactly
two equal, and all distinct gives

```text
1=sum alpha^3+3(sum alpha^2-sum alpha^3)
   +6 sum_(i<j<k) alpha_i alpha_j alpha_k,              (TCP4)
```

which is `(TCE6)`.  The `27` triples, the ranks `13,13,6,14`, the scalar and
multiplicativity identities on the diagonal torus, and `(TCE6)` are checked
by exhaustive exact enumeration in
`experiments/tensor_conjugate_embedding_corner_defect.py`.  The counting
argument above is the proof; the enumeration is an independent check.
