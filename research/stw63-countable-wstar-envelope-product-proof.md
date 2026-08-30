---
rg: 2
id: stw63-countable-wstar-envelope-product-proof
kind: route
title: Put both ranges in a countably generated W-star envelope and split it into separable-predual factors
target: stw63-all-von-neumann-codomains-have-uniqueness
requires:
  - stw63-all-separably-acting-von-neumann-codomains-have-uniqueness
  - stw63-uniqueness-is-closed-under-products
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Fix unital embeddings `phi,psi:Z->M` and form the von Neumann subalgebra

```text
N=W*(phi(Z) union psi(Z)) subset M.                           (1)
```

It has the same unit as `M`.  Since `Z` is norm separable, countable dense
subsets of its two images generate `N` as a W-star algebra.  Thus `N` is
countably generated.

The precise structural input is Elliott--Zsido, *Almost uniformly continuous
automorphism groups of operator algebras*, Journal of Operator Theory 8
(1982), proof of Lemma 4.2 and the explicit final remark on page 275:
every countably generated W-star algebra is a direct product of W-star
algebras with separable predual.  Their proof takes a maximal orthogonal
family of central projections `p_j` for which `Np_j` has separable predual
and proves that their sum is one.  Therefore

```text
N = product_(j in J) N_j,             N_j=Np_j,              (2)
```

with every `(N_j)_*` separable.  This is an algebraic central-product
decomposition; it does not use standard-Borel disintegration or measurable
selection.

The same structural reduction is used explicitly in the primary literature
on map uniqueness: Ciuperca--Giordano--Ng--Niu, *Amenability and uniqueness*,
Proposition 4.3, replaces a von Neumann target by the W-star algebra generated
by countably many map and rank witnesses and then invokes exactly this direct
product of separable-predual algebras.  Their conclusion there is weak-star
uniqueness; the norm conclusion below comes instead from the already proved
norm theorem in every coordinate.

Compressing `phi` and `psi` by `p_j` gives unital maps into `N_j`.  Every
nonzero coordinate map is injective because `Z` is simple.  A von Neumann
algebra with separable predual has a faithful representation on a separable
Hilbert space, so the established separably acting theorem applies in every
coordinate.

Given a finite set `F subset Z` and `epsilon>0`, choose for every `j` a
unitary `u_j in N_j` satisfying

```text
max_(a in F) ||u_j phi_j(a) u_j^* - psi_j(a)|| < epsilon.
```

Then `u=(u_j)_j` is a unitary of `N`, and the norm in (2) is the supremum of
the coordinate norms.  Hence the same inequality holds uniformly in `N`
and therefore in `M`.  Applying this to an increasing sequence of finite
subsets dense in the unit ball of `Z` gives norm approximate unitary
equivalence.  No conditional expectation onto `N`, complementedness of the
inclusion `N subset M`, or extension of coordinate unitaries is required:
`N` is a unital star subalgebra of `M`, so its assembled unitary already is a
unitary of `M`.
