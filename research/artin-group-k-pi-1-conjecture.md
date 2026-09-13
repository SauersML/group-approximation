---
rg: 2
id: artin-group-k-pi-1-conjecture
kind: claim
title: "K(π,1) conjecture: for every finite Coxeter graph the hyperplane orbit space of the Artin group is aspherical"
root: true
---

Let `(W, S)` be a Coxeter system with `S` finite, acting on `V = R^S` by the
geometric representation, with Tits cone `I` and set `𝓗` of reflection hyperplanes.
Put `Ω = (int(I) + iV) − ⋃_{H ∈ 𝓗} H_C`. Then `W` acts freely and properly on `Ω`,
and `π_1(Ω/W) = A_W`, the Artin group of `(W, S)` (H. van der Lek, thesis, 1983).

**Conjecture.** `Ω/W` is a `K(A_W, 1)` for every such `(W, S)`.

Equivalent forms: the Salvetti complex of `(W, S)`, a finite CW complex homotopy
equivalent to `Ω/W`, is aspherical; the modified Deligne complex of `A_W` is
contractible (R. Charney and M. W. Davis, J. Amer. Math. Soc. 8 (1995)).

It is a root because it is a named open problem in its own right. It implies that
every Artin group is torsion-free and of type F (route
`artin-type-f-infinity-via-k-pi-1-conjecture`).

## Attempts

- Known classes (abstract-level check 2026-09-13; see the root
  `zaremsky-1-05-artin-groups-are-type-f-infinity` for citations): spherical, FC, dimension
  ≤ 2, affine, rank three, Huang's tree and cycle classes, every Artin group of dimension 3
  (preprint arXiv:2509.06914).
- Reduction to free-of-infinity parabolic subgroups (Godelle–Paris, arXiv:1007.1365).
- Frontier: dimension 4 diagrams outside the affine, FC and quasi-Lannér classes. Lane
  z1-05-artin-kpi1 is assembling the class the known results give and attacking dimension 4.
