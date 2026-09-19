---
rg: 2
id: group-basis-actions-have-permutation-koopman-spectrum
kind: claim
title: Every group-basis action has permutation Koopman spectrum
distinct_from:
  haar-algebraic-actions-have-permutation-koopman-spectrum: that uses Fourier characters to constrain compact-abelian Haar actions; this applies to every countable group basis, including nonabelian locally finite symmetric and Clifford bases, directly in the canonical group-unitary basis.
  invariant-cartan-group-basis-needs-hyperfinite-envelope: that constrains Cartan-preserving embeddings by measured hyperfiniteness; this gives a representation-theoretic necessary condition for every equivariant embedding, including non-Cartan ones.
  character-group-realizability-parseval-criterion: that decides when one tracial character algebra embeds abstractly in some group factor; this shows why an abstract hyperfinite embedding need not be equivariant for a prescribed action.
---

Let `Gamma` and `K` be countable groups, let
`alpha: Gamma -> Aut(K)`, and let `beta` be the induced action on `L(K)`.
On the canonical orthonormal basis `(u_k)_(k in K)` of `L^2(L(K))`,

```text
beta_g(u_k) = u_(alpha_g(k)).                           (GBK1)
```

Thus the Koopman representation of `Gamma` on `L^2(L(K))` is exactly the
permutation representation of `Gamma` on the countable set `K`.
Consequently, if a finite tracial von Neumann algebra `(D,tau)` with a
trace-preserving `Gamma`-action admits a normal unital trace-preserving
equivariant embedding

```text
Phi: D -> L(K),                                        (GBK2)
```

then its Koopman representation on `L^2(D)` is unitarily equivalent to a
closed subrepresentation of the countable permutation representation
`l^2(K)`.  Indeed, `x -> Phi(x)` extends by trace preservation to an
isometric `Gamma`-intertwiner of the two `L^2` spaces.  This conclusion does
not require `K` to be amenable and does not require `Phi(D)` to be Cartan.
It is therefore a necessary condition for every amenable group-basis
crossed-product compiler

```text
D rtimes Gamma -> L(K) rtimes Gamma = L(K rtimes Gamma)
```

which sends the actor unitaries to the canonical actor unitaries.

The condition is a genuine obstruction, not an automatic separability
fact.  For example, let `Gamma=Z` act by an irrational rotation of the
circle.  Its Koopman representation has an eigenvector with eigenvalue
`exp(2 pi i theta)`, where `theta` is irrational.  A countable permutation
representation of `Z` is the orthogonal sum over its orbits: a finite orbit
has only root-of-unity eigenvalues, while an infinite orbit is a bilateral
shift and has no eigenvectors.  Hence this pmp action cannot embed
equivariantly into `L(K)` for **any** countable group `K` acted on by group
automorphisms.

This isolates equivariance as the whole universal-encoding failure.  In the
absence of an action, every standard probability algebra embeds unitally and
trace-preservingly into `L(S_fin(N))`: the finitary symmetric group is
countable, amenable and ICC, so its group factor is the hyperfinite `II_1`
factor, which contains every separable abelian finite von Neumann algebra
with its prescribed trace.  Thus arbitrary atomic weights and arbitrary
nonatomic measures are available abstractly; one cannot in general choose
the embedding to intertwine a prescribed action by group-basis
automorphisms.

For the two most concrete proposed bases this becomes finite-pattern
spectrum.

* If `K=S_fin(Y)` and `Gamma` acts by permuting `Y`, then `K` is the union of
  its finite-support permutation patterns, and `l^2(K)` is the sum of the
  corresponding quasi-regular representations
  `l^2(Gamma/Stab_Gamma(sigma))`.
* If `K` is a countable Pauli/Clifford lamp group, every genuine group
  automorphism again permutes its canonical words.  Cutting by a fixed
  finite central character merely changes a choice of coset representatives
  into a finite-phase signed permutation basis; as a subspace of `L^2(L(K))`
  it still satisfies `(GBK1)`.  General Bogoliubov automorphisms that mix
  this basis linearly evade the statement only by ceasing to be group-basis
  automorphisms, in which case the crossed product is no longer canonically
  `L(K rtimes Gamma)`.

Therefore locally finite symmetric and CAR/UHF group bases do **not** give a
universal exact algebraic envelope for arbitrary invariant measures.  For a
specific non-Connes-embeddable relation the remaining live test is whether
the particular base action's Koopman representation embeds in a countable
permutation representation; passing this test is necessary, not sufficient,
because multiplication and normalizer coherence are additional constraints.
