---
rg: 2
id: stw31-closure-of-compacts-module-construction-proof
kind: route
title: Build a projection-exhausted module from every algebraic Cu decomposition
target: stw31-algebraic-module-rigidity-forces-real-rank-zero
requires: []
artifacts:
  - research/artifacts/stw31-module-rigidity-frontier-audit-2026-08-30.md
---

# Build a projection-exhausted module from every algebraic Cu decomposition

Let `A` be separable and stably finite.

## 1. The nested-projective model

Let

```text
x=sup_n c_n
```

in `Cu(A)`, where the `c_n` are compact and increasing. By
Brown--Ciuperca, choose an algebraically finitely generated projective
Hilbert module `P_n` representing `c_n`. Since `c_n<=c_(n+1)` and `c_n` is
compact, `P_n` is isomorphic to a compactly contained submodule of
`P_(n+1)`. Choose isometric connecting maps with those images and form the
resulting isometric direct system, written as

```text
P_1 subset-subset P_2 subset-subset ... .
```

Let `F` be the Hilbert-module completion of their algebraic union. The
CEI construction of sequential suprema gives

```text
[F]=sup_n [P_n]=x.                                    (1)
```

Let `i_n:P_n->F` be the canonical isometry. Since `P_n` is algebraically
finitely generated projective, `id_(P_n)` belongs to `K(P_n)`, and `i_n` is
adjointable. Hence

```text
e_n=i_n i_n^*
```

is the orthogonal projection onto `i_n(P_n)` and belongs to `K(F)`. The
nested direct system makes these projections compatible, so

```text
e_1<=e_2<=...,
e_n xi -> xi                    for every xi in F.
```

It follows first on rank-one operators, and then by density, that
`(e_n)` is a projection approximate identity for `K(F)`.

## 2. Apply the model to a hereditary subalgebra

Let `a` be positive in `A tensor K` and put

```text
E=H_a=closure(a ell^2(A)).
```

Algebraicity of `Cu(A)` supplies compact increasing `c_n` with
`[E]=sup c_n`. Apply Step 1 to obtain `F` with `[F]=[E]` and with a
projection approximate identity in `K(F)`.

If `A` is projection-exhausted closure-rigid, then `E` and `F` are
isomorphic.
Conjugating compact endomorphisms by this module isomorphism identifies
`K(E)` and `K(F)`, so `K(E)` has a projection approximate identity. Under
the standard realization of `H_a`,

```text
K(E) is isomorphic to Her(a).
```

Every hereditary subalgebra of `A tensor K` is sigma-unital and is of this
form because `A` is separable. Therefore every hereditary subalgebra of
`A tensor K` has a projection approximate identity. The hereditary
characterization of real rank zero gives

```text
RR(A tensor K)=0,
```

and real rank zero passes to the corner `A`.

## 3. Contrapositive and the exact obstruction

Assume instead that `Cu(A)` is algebraic and `RR(A)>0`. Choose a
sigma-unital hereditary subalgebra `B=Her(a)` of `A tensor K` with no
projection approximate identity, and set `E=H_a`. For any increasing
compact decomposition of `[E]`, Step 1 gives `F` satisfying (1) with
`K(F)` projection-exhausted.

If `E` and `F` were isomorphic, then `K(E)=B` would inherit a projection
approximate identity, a contradiction. Hence `E` and `F` are
CEI-equivalent but nonisomorphic. This proves the counterexample
certificate and shows that the obstruction is entirely at the
infinite-stage coherence step.
