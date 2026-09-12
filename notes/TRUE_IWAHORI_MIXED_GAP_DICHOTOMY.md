# The Iwahori edge defect has a mixed-gap/sparse-kernel dichotomy

Date: 2026-08-13

## 1. Outcome

Let `rho,sigma:B->U(d)` be the two exact Iwahori edge restrictions. Their
pointwise closeness makes the identity matrix an almost invariant vector for
the exact mixed representation

```text
lambda(b)(T)=rho(b) T sigma(b)^*                       (MGD1)
```

on normalized Hilbert--Schmidt space. Orthogonal projection onto the exact
invariant space gives an exact intertwiner. If `(MGD1)` has a uniform
spectral gap away from its invariant space, this intertwiner is close to the
identity and its failure to be invertible is confined to vanishing relative
dimension.

Thus every unresolved Iwahori sequence has one of two sharply different
pathologies:

1. the mixed edge spectral gap collapses; or
2. the gap stays open, but a sparse kernel/cokernel representation cannot be
   extended compatibly through the two index-three vertices.

The second alternative explains why robust ambient spectral gap alone does
not finish the problem: normalized HS norm permits a nonzero exact
representation-theoretic mismatch on `o(d)` dimensions.

## 2. Quantitative projection theorem

Let `B=<S>` with `S=S^(-1)` finite. For exact unitary representations

```text
rho,sigma:B->U(d)                                      (MGD2)
```

put

```text
H=HS_d=M_d(C),
Inv={T in H : rho(b)T=T sigma(b) for every b in B}.    (MGD3)
```

Use the normalized Hilbert--Schmidt norm, so `||1_d||_2=1`, and define

```text
E(T)=|S|^(-1) sum_(s in S)
     ||rho(s)T-T sigma(s)||_2^2.                       (MGD4)
```

Let `P:H->Inv` be orthogonal projection. Say that the mixed representation
has gap `kappa>0` if

```text
E(T)>=kappa ||T||_2^2,             T perpendicular Inv. (MGD5)
```

**Theorem 1 (mixed-gap projection).** Suppose

```text
max_(s in S)||rho(s)-sigma(s)||_2<=delta.              (MGD6)
```

Set `T_0=P(1_d)`. Then:

```text
rho(b)T_0=T_0 sigma(b),                  b in B,       (MGD7)
||1_d-T_0||_2^2<=delta^2/kappa.                       (MGD8)
```

If `q` and `p` are the support projections of `T_0^*T_0` and
`T_0T_0^*`, respectively, then

```text
tr_d(1-q)=tr_d(1-p)<=delta^2/kappa.                    (MGD9)
```

The polar part `V:q C^d -> p C^d` is a unitary between its support spaces
and exactly intertwines the compressed edge representations:

```text
rho(b)V=V sigma(b)       on q C^d,       b in B.       (MGD10)
```

If `T_0` is invertible, `V` is a unitary on `C^d`; conjugating `sigma` by
`V` makes the two edge restrictions exactly equal. More generally, the same
conclusion holds if the kernel representation of `sigma` and the cokernel
representation of `rho` are unitarily equivalent as `B`-representations.

### Proof

Equation `(MGD7)` is the definition of `P`. From `(MGD6)`,

```text
E(1_d)<=delta^2.                                       (MGD11)
```

Since `P` is the orthogonal projection onto `Inv`, the vector
`1_d-T_0` is perpendicular to `Inv`. Also `E(T_0)=0`, and the Laplacian
associated with `(MGD4)` annihilates `Inv`, so

```text
E(1_d-T_0)=E(1_d).                                     (MGD12)
```

Apply `(MGD5)` to `(MGD12)` and use `(MGD11)` to obtain `(MGD8)`.

On `ker(T_0)`, the operator `1_d-T_0` is the identity. Therefore

```text
rank ker(T_0)/d<=||1_d-T_0||_2^2.                      (MGD13)
```

The kernel and cokernel of a square matrix have the same dimension, proving
`(MGD9)`.

From `(MGD7)`, `T_0^*T_0` commutes with `sigma(B)` and `T_0T_0^*`
commutes with `rho(B)`. Hence their support projections are invariant and
the polar decomposition `T_0=V|T_0|` gives `(MGD10)`. If `T_0` is
invertible, `p=q=1`. If the two complementary representations are
equivalent, extend `V` by a unitary intertwiner between them. End proof.

## 3. Sequential Iwahori consequence

Let

```text
alpha_n,beta_n:SL_2(Z)->U(d_n)                         (MGD14)
```

be an Iwahori pair with defect `delta_n->0`, and apply Theorem 1 to

```text
rho_n=alpha_n|B_+,
sigma_n=(beta_n|B_-) composed sigma.                   (MGD15)
```

Write `kappa_n` for the mixed gap. After passing to a subsequence, exactly
one of the following reductions applies.

### Gap-collapse branch

```text
kappa_n->0.                                            (MGD16)
```

There are normalized matrices perpendicular to all exact edge
intertwiners whose mixed edge energy tends to zero. This is a genuine
almost-invariant-vector problem for the virtually-free edge representation;
ambient adjoint spectral gap does not see these mixed vectors.

### Sparse-kernel branch

There is `kappa>0` with `kappa_n>=kappa`. Then the two edge restrictions are
exactly intertwined away from invariant kernel and cokernel spaces of
relative dimension at most

```text
delta_n^2/kappa -> 0.                                  (MGD17)
```

If those complementary `B_+`-representations are equivalent for all large
`n`, the original pair is made exactly compatible by conjugation alone.
Thus a negative sequence in this branch must carry a nonzero, vanishing-rank
restriction-semiring mismatch. The remaining question is whether this
sparse mismatch can always be absorbed by `o(d_n)` vertex representations
which extend through both index-three copies of `SL_2(Z)`.

## 4. Relation to the previous reductions

The dimension-tight theorem rules out bounded-dimensional irreducible mass
as the source of a negative sequence. The present theorem adds that, in the
remaining high-dimensional central-regular sector, failure is not diffuse
unless the mixed gap collapses. With a uniform mixed gap, all incompatibility
is carried by a vanishing-rank exact edge representation.

This does not yet prove Iwahori matching. A `B_+`-invariant sparse subspace
need not be invariant under either modular vertex, and its orbit under the
amalgam can spread through the whole matrix space. Treating `(MGD17)` as if
it were already removable padding would assume the missing finite-index
extension theorem.

## References

- `TRUE_IWAHORI_MATCHING_FIXED_TYPE_REDUCTION.md`.
- `FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md`.
