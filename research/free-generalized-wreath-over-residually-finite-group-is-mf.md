---
rg: 2
id: free-generalized-wreath-over-residually-finite-group-is-mf
kind: claim
title: The free generalized wreath product of Z over any action of a countable residually finite group is MF, so every free-kernel tree extension of a residually finite group is MF
distinct_from:
  infinite-cyclic-compression-lamp-mf: that proves MF for commuting integer lamps over one coset space H/L_1 with L_1 finitely generated; this proves it for free integer lamps over an arbitrary countable Q-set, with any number of orbits and arbitrary stabilizers, using the same slow-bump idea with a finite-dimensional unitary block per lamp instead of a scalar phase.
  symmetric-double-weak-mf: that proves symmetric doubles G *_Gamma G of residually finite groups are weak MF through Shulman's C-star amalgam theorem, which with sl3-hnn-sits-in-shulman-symmetric-double covers the one-orbit free wreath <Q,t | [t,H]=1>; this is a direct corona construction with no C-star amalgam input and covers several orbits at once, which is what free-kernel tree extensions such as Radu's lattice need.
  gkp-free-generalized-wreath-soficity: that is the soficity permanence for free generalized wreath products over sofic set actions; this is the operator-norm MF permanence over residually finite groups, with no hypothesis on the set action, and it gives no soficity and no hyperlinearity.
  free-kernel-tree-actions-embed-in-free-generalized-wreath: that supplies the embedding of free-kernel tree actions into free generalized wreath products; this supplies the MF permanence which that embedding transports.
---

**ESTABLISHED.** Let `Q` be a countable residually finite group and `X` a countable `Q`-set. Then

```text
W = Z ≀^*_X Q = ( *_(x ∈ X) Z_x ) ⋊ Q ,       q Z_x q^(-1) = Z_(qx),
```

is MF: it embeds in the unitary group of a norm-matrix corona
`prod_n M_(d_n)(C) / (+)_n M_(d_n)(C)`.

**Corollary (free-kernel tree extensions).** Let a countable group `Γ` act on a tree, and let
`Λ ◁ Γ` act freely, fixing no vertex and inverting no edge. If `Γ/Λ` is residually finite,
then `Γ` is MF.

Proof of the corollary: `free-kernel-tree-actions-embed-in-free-generalized-wreath` (item 1)
embeds `Γ` in `Z ≀^*_(E^±(Y)) (Γ/Λ)`, and subgroups of MF groups are MF.

Special cases:
- every subgroup-centralizer HNN extension `<A, t | [t,C]=1>` of a countable residually finite
  `A` is MF (`centralizer-hnn-is-free-generalized-wreath`);
- the non-residually-finite Radu lattice is MF (`radu-bmw-lattice-is-mf`).

**Why it matters.** Free-by-(residually finite) groups acting on trees include the known small
non-residually-finite lattices in products of trees that are lifts of arithmetic lattices. Their
failure of residual finiteness, and their finite-residual marks, are invisible to operator-norm MF.

**What it does not give.** The models separate each element at a vanishing fraction of the
coordinates. So the theorem gives no Hilbert--Schmidt statement, and in particular neither
hyperlinearity nor soficity. This matches `kt-pair-group-double-is-nonsofic`: the Kun--Thom double
embeds in a one-orbit instance and is nonsofic.

Proof in `free-generalized-wreath-over-residually-finite-group-is-mf-proof`.
