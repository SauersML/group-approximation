---
rg: 2
id: centralized-gram-row-words-upgrade-trace-gap-to-vector-gap
kind: claim
title: Centralizing finitely many Gram-row words upgrades their trace gap to every vector state
distinct_from:
  conjugation-invariant-clause-energy-twirls-vector-states: that assumes an invariant aggregate energy and uses Haar twirling plus compactness; this gives an ordinary finite group presentation which makes each already-wordized row a singleton orbit and derives an operator inequality directly
  partial-isometry-swap-wordizes-one-bcs-gram-row: that turns one matrix Gram residual into one ordinary word defect; this promotes any finite family of those trace-level word gaps to whole-vector-state soundness
  two-letter-dihedral-swap-wordizes-one-gram-row: that avoids manufacturing a hybrid block letter for one consistency row; this centralizes the resulting literal row words without changing their exact perfect realization
  central-word-state-face-compiler: that must additionally preserve a scalar phase and encode nonlinear predicates on the whole face; this solves only the finite vector-versus-trace promotion once trace-level row soundness is available
---

Let `Gamma=<S|R>` be a finitely generated group, let `y` be a central
involution, put `p=(1-y)/2`, and let `q_1,...,q_m` be ordinary words in the
generators.  Form the finite presentation

```text
Gamma_cen
 =<S | R, [q_j,s]=1 (1<=j<=m, s in S)>.               (CGV1)
```

In `C*(Gamma_cen)` put

```text
D=sum_j (q_j-1)^*(q_j-1).                              (CGV2)
```

Then `D` is central.  Suppose there is `delta>0` such that every
finite-dimensional representation `pi` of `Gamma_cen` satisfies the
normalized-trace inequality

```text
tr(pi(D)) >= delta tr(pi(p)).                           (CGV3)
```

Then every such representation satisfies the operator inequality

```text
pi(D) >= delta pi(p),                                  (CGV4)
```

and hence every vector `xi` satisfies

```text
sum_j ||(pi(q_j)-1)xi||^2
 >= delta ||pi(p)xi||^2.                               (CGV5)
```

The construction is exact-completeness neutral: every representation of
`Gamma` in which all `q_j=1` extends across the same generator assignment to
`Gamma_cen`.  Thus when the `q_j` are the Gram-row words from
`partial-isometry-swap-wordizes-one-bcs-gram-row` or
`two-letter-dihedral-swap-wordizes-one-gram-row`, the standard-form perfect
BCS model survives unchanged.

This is an ordinary finite group-word gadget.  Each `q_j` is a singleton
conjugacy orbit under every decoded generator, so `(CGV2)` is a special case
of the invariant clause energy in
`conjugation-invariant-clause-energy-twirls-vector-states`.  It assumes no
common reducing projection for the BCS context observables and introduces no
matrix-only operation.

## Consequence for the common-swap decoder

Suppose a finite common-swap packet supplies one central marked sector `p`,
one common partial isometry `S_0`, and row words `q_j` such that the established
word comparisons and the finite BCS game gap give `(CGV3)`.  Apply `(CGV1)`.
Then `(CGV5)` is whole-vector-state soundness: any vector with positive marked
mass pays a proportional sum of literal word defects.  A common reducing
intersection of the context carriers is not used; their coupling occurs only
through the common Gram source already present in the row words.

The theorem does **not** manufacture `(CGV3)`.  In the current common-swap
programme, consistency rows are already literal two-letter words, while the
nonlinear predicate/source-saturation inequality `(CPS9)` remains open.
Centralization promotes that inequality once proved but cannot make separately
selected context carriers overlap.  It is therefore a complete solution of
the vector-versus-trace part of Property 2, not of the global phase or
predicate compiler.

