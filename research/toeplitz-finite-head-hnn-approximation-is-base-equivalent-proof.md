---
rg: 2
id: toeplitz-finite-head-hnn-approximation-is-base-equivalent-proof
kind: route
title: Pass to the direct limit, compute the symbol action, and use amenable-quotient permanence
target: toeplitz-finite-head-hnn-approximation-is-base-equivalent
requires:
  - toeplitz-finite-head-extension-preserves-root
  - ascending-hnn-cannot-create-nonhyperlinearity
  - schur-toeplitz-root-mark-is-fd-invisible
  - schur-idempotent-is-an-injective-toeplitz-defect
---

Write `G_infinity=colim(G,beta)`.  Injectivity of `beta` gives

```text
K=G_infinity semidirect Z.                                 (1)
```

If `bar(c)` denotes the Laurent symbol of `c in T`, then

```text
overline(beta(c))
 = z bar(c) z^(-1)+epsilon(c) overline(P)
 = bar(c),                                                  (2)
```

because the symbol ring is commutative and `overline(P)=0`.  Hence the symbol
map is compatible with the direct system and the stable letter acts trivially
on its image.  The coefficient symbol map is onto: `X` and `Y` map to `z` and
`z^(-1)`, respectively.  It follows directly on elementary root generators
that `G->EL_5(k[z,z^(-1)])` is onto.  Combining symbol and height gives the
quotient map in `(FHE1)`.
Its kernel is the direct limit of the symbol kernels.  Each symbol kernel is
locally finite by `toeplitz-finite-head-extension-preserves-root`, and a
directed union of locally finite groups is locally finite.  The quotient
`Q x Z` is residually finite because `Q` is a subgroup of the residually
finite group `EL_5(k[z,z^(-1)])`.

If `K` is hyperlinear or sofic, then so is its subgroup `G`.  Conversely, if
`G` has either property, so does its directed union `G_infinity`.  Extensions
of a hyperlinear group, respectively a sofic group, by an amenable quotient
are hyperlinear, respectively sofic.  Apply this to `(1)` and the quotient
`Z`.  This proves both equivalences in `(FHE2)`; it uses no permanence theorem
in the opposite amenable-normal direction.

Every homomorphism from `K` to a finite group, followed by that finite group's
left regular representation, is a finite-dimensional unitary representation.
Precomposing with the natural map from the Schur--Toeplitz group and applying
`schur-toeplitz-root-mark-is-fd-invisible` kills the marked root.  The root is
nontrivial by `toeplitz-finite-head-extension-preserves-root`, so it lies in
the finite residual and `K` is not residually finite.

For the last assertion, a coefficient homomorphism `T->D` into a directly
finite ring sends the relation `YX=1` to a two-sided inverse relation, hence
sends `XY` to `1`.  The relation `1-XY=eta(P)` then kills `eta(P)`.  Entrywise
application therefore sends `x_12(eta(P))` to the identity.  Finite rings are
directly finite, so this includes every finite-ring periodization.  It does
not exclude nonlinear partial group models, which is why no LEF, sofic, or
hyperlinear verdict for the base is asserted.
