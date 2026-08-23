---
rg: 2
id: selected-odd-heisenberg-corner-normal-form-proof
kind: route
title: Cut the group-algebra amalgam by the central character and identify the Heisenberg block
target: selected-odd-heisenberg-corner-is-native-matrix-amalgam
requires:
  - affine-leavitt-p-heisenberg-graft-kills-fd-four-cap-corner
  - amenable-edge-graph-corners-cannot-groupify-a-nonce-game
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
---

Put

```text
A=C[Gamma_A x <c>],
D=C[<w,c>],
H=C[H_p].                                               (OHN1)
```

The group algebra of the group amalgam is the algebraic star amalgam

```text
C[Lambda_p]=A *_D H.                                   (OHN2)
```

The element `c` is central in both vertex groups, hence in `Lambda_p`, so
`e=e_chi` is a central projection in every algebra in `(OHN2)`.  Cutting the
universal property of `(OHN2)` by this common central projection gives

```text
e C[Lambda_p] e=(eAe) *_(eDe) (eHe).                   (OHN3)
```

Indeed the complementary central sectors have zero cross-products, and a
pair of corner-unital maps agreeing on `eDe` extends by zero on `1-e` to
maps from the two vertex algebras; the universal properties in both
directions are inverse.

Because the first vertex is a direct product,

```text
eAe isomorphic to C[Gamma_A].                           (OHN4)
```

Since `<w,c>=C_p^2`, fixing the `c` character leaves

```text
eDe isomorphic to C[<w>].                               (OHN5)
```

Finally, the finite Heisenberg group has one irreducible representation of
dimension `p` for each nontrivial central character.  Its `chi` block is
therefore

```text
eHe isomorphic to M_p(C).                               (OHN6)
```

Equations `(OHN3)--(OHN6)` prove `(OHM1)`.

The identity coefficient of `e` is `1/p`.  On the first vertex,
`tau(e g)/tau(e)=delta_(g,1)` for `g in Gamma_A`.  On the Heisenberg vertex,
the canonical trace weight of the selected simple block is `1/p`, so its
normalized restriction is the unique normalized matrix trace.  Nontrivial
powers of `w` have trace zero on both sides.  This proves `(OHM2)`.

If a no-CE algebra mapped unitally into this corner, canonical corner trace
promotion would make `Lambda_p` nonhyperlinear.  If `Gamma_A` were
hyperlinear, then `Gamma_A x C_p` and `H_p` would be hyperlinear and the
edge `C_p^2` is amenable; the amenable-edge permanence theorem would make
`Lambda_p` hyperlinear, a contradiction.  This proves `(OHM4)` and the
claimed reduction.
