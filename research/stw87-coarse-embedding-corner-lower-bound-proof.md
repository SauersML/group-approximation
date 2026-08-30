---
rg: 2
id: stw87-coarse-embedding-corner-lower-bound-proof
kind: route
title: Label the uniformly finite fibres and conjugate onto a diagonal matrix corner
target: stw87-coarse-embedding-corner-lower-bound
requires:
  - stw87-wz-upper-bound
---

Let `f:Y→X` be a coarse embedding.  Effective properness gives `R₀<∞`
such that

```text
f(y)=f(y')  ⇒  d_Y(y,y')≤R₀.
```

Bounded geometry of `Y` therefore gives a uniform finite bound `N` on the
fibres of `f`.  Choose a label `c(y)∈{1,...,N}` which is injective on each
fibre, and define an isometry

```text
V:ℓ²(Y)→ℓ²(X)⊗ℂ^N,
Vδ_y=δ_f(y)⊗e_c(y).
```

Its range projection `p=VV*` is diagonal, hence belongs to
`M_N(ℓ∞(X))`.

If `T` has propagation at most `R` on `Y`, bornology of `f` supplies `S`
such that

```text
d_Y(y,y')≤R  ⇒  d_X(f(y),f(y'))≤S.
```

Thus `VTV*` is a finite-propagation element of `pM_N(C*_u(X))p`.
Conversely, for every `S` effective properness supplies `R` such that

```text
d_X(f(y),f(y'))≤S  ⇒  d_Y(y,y')≤R.
```

Hence pulling a finite-propagation matrix operator in the corner back by
`V* (·) V` gives a finite-propagation operator on `Y`.  Compressing
finite-propagation approximants by `p` and taking norm closures proves

```text
Ad(V)(C*_u(Y))=pM_N(C*_u(X))p.
```

Nuclear dimension is unchanged by finite matrix amplification and does not
increase on hereditary subalgebras, proving the inequality.  A coarse
equivalence gives coarse embeddings in both directions and hence equality of
the two nuclear dimensions.  The first final assertion combines the lower
bound with the Winter--Zacharias upper bound; the second follows because one
finite nuclear-dimension bound for `C*_u(X)` would bound every corner.
