---
rg: 2
id: agent-stw77-zero-type-i-proper-support-models-proof
kind: route
title: Infinitely amplify a local model and absorb it fibrewise
target: agent-stw77-zero-type-i-proper-support-models
requires:
  - zero-dimensional-unital-maps-are-locally-fd
  - stw77-type-i-von-neumann-targets-solve-map
---

Fix a finite set `F` of contractions and `epsilon>0`.  The one-sided local
finite-dimensional theorem gives a unital finite-dimensional algebra
`D subset M` and elements `d_a in D` such that

```text
max_(a in F)||d_a-phi(a)||<epsilon/3.                 (1)
```

Use a standard direct-integral realization

```text
M=integral_X^direct B(H_x) d mu(x).
```

Write `phi_x` and `pi_x:D->B(H_x)` for the fibre representations.  By
separability of `A` and finite dimensionality of `D`, delete one common null
set on which the fibre maps fail to be homomorphisms.  The essential-fibre
argument in the proof of
`stw77-type-i-von-neumann-targets-solve-map` then shows that every `H_x` is
infinite dimensional and `phi_x` is essential.

Here is the exact use of pointwise proper infiniteness.  For a norm-dense
positive sequence `(a_n)` and rational `r>0`, consider

```text
X_(n,r)={x: ||phi_x(a_n)||>r and ||phi_x(a_n)||_ess<r}.
```

The norm and essential norm fields are measurable.  If nonessential fibres
had positive measure, some fixed `X_(n,r)` would have positive measure.  For
`c=(a_n-r)_+`, the operator `phi_x(c)` is nonzero and finite rank on this
set: its spectrum above `r` is finite because the essential norm is below
`r`.  Global Cuntz witnesses for proper infiniteness of `phi(c)` disintegrate
to witnesses almost everywhere, contradicting finite rank on `X_(n,r)`.
Finite-dimensional fibres are excluded in the same way using `phi(1)=1`.

Put `K_x=l2 tensor H_x`.  On `K_x` consider the countable amplifications

```text
phi_x^(infinity)=1 tensor phi_x,
pi_x^(infinity)=1 tensor pi_x.
```

Let `C_x=phi_x(A)`.  Voiculescu absorption for the faithful essential
inclusion `C_x->B(H_x)`, applied to its countable amplification, gives
unitaries from `H_x direct_sum K_x` to `H_x` which absorb
`phi_x direct_sum phi_x^(infinity)`.  A coordinate reindexing
`K_x->H_x direct_sum K_x` exactly intertwines `phi_x^(infinity)` with that
direct sum.  Composing the two unitaries gives `U_x:K_x->H_x` satisfying

```text
max_(a in F)
 ||U_x phi_x^(infinity)(a) U_x^*-phi_x(a)||<=epsilon/3.  (2)
```

The unitaries may be chosen measurably.  First measurably trivialize the
infinite-dimensional field `(H_x)` (and hence `(K_x)`).  In the strong-star
unit balls, the relation consisting of the unitary equations and the
non-strict bounds in `(2)` is Borel: each operator norm is the supremum over
a fixed countable dense set of vectors.  Its sections are nonempty and
closed.  Jankov--von Neumann selection gives a universally measurable
selector, which may be replaced almost everywhere by a measurable operator
field.  This is the same measurable-absorption selection used in the
established type-I target proof.

Define

```text
rho_x(d)=U_x pi_x^(infinity)(d) U_x^*,
rho=integral_X^direct rho_x d mu(x):D->M.              (3)
```

Checking `(3)` on a fixed finite basis of `D` proves measurability and hence
that `rho` is a unital homomorphism.  Combining `(1)` and `(2)` gives

```text
||rho(d_a)-phi(a)||
 <= ||d_a-phi(a)||
    + ess_sup_x ||U_x phi_x^(infinity)(a)U_x^*-phi_x(a)||
 <2 epsilon/3.                                        (4)
```

In fact `rho` is injective, because direct-integral faithfulness of the given
inclusion `D subset M` gives

```text
||rho(d)||=ess_sup_x ||1 tensor pi_x(d)||
          =ess_sup_x ||pi_x(d)||=||d||.                (5)
```

Set `E=rho(D)`.  Let `q` be a minimal projection of `D` and put
`p=rho(q)`.  Formula `(3)` gives

```text
p(x)=U_x(1 tensor pi_x(q))U_x^*.
```

For almost every `x`, this projection is either zero or has infinite rank:
the countable amplification of every nonzero projection has infinite rank.
A decomposable projection in a type-I von Neumann algebra whose nonzero
fibres all have infinite rank is properly infinite.  Choose a measurable
orthonormal basis `(xi_n(x))` of `p(x)H_x` on its support and define

```text
v_0(x)xi_n(x)=xi_(2n)(x),
v_1(x)xi_n(x)=xi_(2n+1)(x).
```

Extended by zero off `p(x)H_x`, these are measurable fields with
`v_i^*v_i=p` and orthogonal range projections below `p`.  Hence every
minimal projection of `E` is properly infinite.

The bound `(4)` proves the claim (and leaves room to absorb noncontractive
finite packets by rescaling).  Taking each block of `E` as a singleton
cluster gives zero coordinate variation and properly infinite aggregate
rank-one support, exactly as required by the clustering claim.

## Dependency boundary

The proof uses the local finite-dimensional model theorem, Voiculescu
absorption, and measurable selection.  It does not use O-infinity-stability
as a black box: the dependency on the type-I target node is specifically its
already-proved essential-fibre and measurable-absorption mechanism.

The construction takes place inside the von Neumann target `M`.  Applying it
inside `B**` for a general C-star target `B` does not return the homomorphism
`rho:D->B**` to `B`; Kaplansky density gives only strong-star approximation,
whereas `(4)` and the central-isometry criterion require operator norm.
