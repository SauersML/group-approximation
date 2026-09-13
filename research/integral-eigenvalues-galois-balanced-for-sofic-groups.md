---
rg: 2
id: integral-eigenvalues-galois-balanced-for-sofic-groups
kind: claim
title: Over a sofic group the eigenvalues of integral matrices are algebraic integers with equal conjugate multiplicities
distinct_from:
  integral-group-ring-eigenvalues-are-galois-balanced: that is the open statement for every group; this is Thom's sofic case, imported from the literature
  determinant-conjecture-holds-for-sofic-groups: that is the Elek--Szabó determinant bound for sofic groups; this is Thom's eigenvalue theorem for the same class, which the determinant bound alone does not give
---

**ESTABLISHED (literature import)** by
`integral-eigenvalues-galois-balanced-for-sofic-citation`.

A. Thom, *Sofic groups and diophantine approximation*, arXiv:math/0701294v3
(29 Jan 2007), page 1, read from the PDF:

> **Theorem 1.1.** Let `Γ` be a sofic group and `A ∈ M_n(ZΓ)`. Consider the
> natural action of `M_n(ZΓ)` on the Hilbert space `ℓ^2Γ^(⊕n)` by left
> convolution. Denote by `λ(A)` the corresponding bounded operator.
> (i) All eigenvalues of the `λ(A)` are algebraic integers.
> (ii) If `α ∈ C` is an eigenvalue of the operator `λ(A)`, then all its Galois
> conjugates are also eigenvalues and the corresponding eigenspaces have the same
> von Neumann dimension.

**Total reality.** For self-adjoint `A`, every eigenvalue is real. By (ii) all
conjugates are eigenvalues, hence real. So over sofic groups
`integral-group-ring-eigenvalues-are-galois-balanced` holds.

Right multiplication, used elsewhere in the graph, gives the same eigenvalues
and kernel dimensions as left convolution, through the involution `g -> g^-1`.
