---
rg: 2
id: one-mf-black-hole-has-universal-outer-symmetry-proof
kind: route
title: Permute the star factors and use nonconjugacy of distinct vertex groups
target: one-mf-black-hole-has-universal-outer-symmetry
requires:
  - permutation-camouflage-realizes-countable-actions
  - one-universal-kernel-realizes-all-countable-mf-reflections
  - mf-radical-functoriality
---

Every permutation `sigma of X` extends uniquely to an automorphism
`alpha_sigma` of `K_X` by sending `B_x` identically onto `B_(sigma x)` and
fixing the common subgroup `D` pointwise.  This gives a homomorphism
`Sym(X)->Aut(K_X)`.

Distinct vertex groups `B_x` and `B_y` are not conjugate in `K_X`.  Indeed,
in the Bass--Serre tree of the star amalgam, `B_x` fixes its distinguished
vertex and contains an element outside the incident edge group `D`, so its
fixed set is exactly that vertex.  The `K_X`-action preserves the vertex
type indexed by `x`.  Hence a conjugacy `g B_x g^(-1)=B_y` forces `x=y`.

If `alpha_sigma` were inner, conjugation by its implementing element would
send every `B_x` to `B_(sigma x)`.  The preceding nonconjugacy forces
`sigma x=x` for every `x`, so `sigma` is the identity.  Thus the composite
`Sym(X)->Out(K_X)` is injective, proving `(UOS1)`.

The center of `K_X` is trivial.  A central element normalizes every `B_x`;
the same tree argument puts it in every vertex group and hence in `D`.
Inside any one factor it is central in `B`, whose center is trivial because
`B` is nonabelian simple.  The remaining structural properties of `K_X`
follow from the universal-kernel theorem.

Every countable group embeds in `Sym(X)` by its regular permutation action
(extend a finite regular action by fixed points when necessary), which gives
`(UOS2)`.  The lifts to `Aut(K_X)` are the factor-permutation automorphisms.
The radical and semantic-closure statements for the semidirect products are
the arbitrary permutation-camouflage theorem.  When `Q` is MF, its inverse
image radical is exactly `K_X`; full invariance of the MF radical makes this
kernel characteristic.

For the final assertion, let `S` range over the infinite subsets of the
prime numbers and put

```text
Q_S=directSum_(p in S) C_p.
```

These are countably infinite amenable abelian MF groups, and different `S`
give nonisomorphic groups because `S` is recovered from the element orders.
There are continuum many such `S`.  Their camouflaged split extensions all
have the same kernel `K_infinity`, while an isomorphism of two extensions
would induce an isomorphism of their canonical MF-radical quotients.  Hence
the extensions are pairwise nonisomorphic.

---
