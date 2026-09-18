---
rg: 2
id: non-elementary-hyperbolic-groups-are-contracting-rsgs
kind: claim
title: Every non-elementary hyperbolic group is isomorphic to a contracting rational similarity group (BBMZ-hyperbolic Question 1.1)
distinct_from:
  hyperbolic-groups-embed-in-contracting-rsgs: that is the established embedding of every hyperbolic group into a contracting RSG; this asks for an isomorphism with no free factor added.
  free-products-with-a-finite-factor-are-contracting-rsgs: that is the case of a finite free factor, established; this is the whole question.
  contracting-rsgs-closed-under-products-with-finite-groups: that is a closure lemma used for the known cases; this is the question itself.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**OPEN.** This is Question 1.1 of Belk--Bleak--Matucci--Zaremsky, *Hyperbolic groups satisfy
the Boone--Higman conjecture*, arXiv:2309.06224v3 (§1, `ssec:open`, read in the TeX):
"Is every non-elementary hyperbolic group isomorphic to a contracting RSG?"

## Known cases (on main)

- **`G * Z`** for every hyperbolic `G` (BBMZ `thrm:FreeProductBoundary` together with
  `thrm:contracting`; BBMZ state this as "if `G` has `Z` as a proper free factor then the RSG
  is contracting").
- **`G * F`** for every nontrivial hyperbolic `G` and nontrivial finite `F`, not
  `Z/2 * Z/2`. This is `free-products-with-a-finite-factor-are-contracting-rsgs`, a lane
  proof. It includes every free product of finite groups, such as `PSL_2(Z)`.
- **Direct products with finite groups** of any of the above:
  `contracting-rsgs-closed-under-products-with-finite-groups`, a lane proof. It includes
  groups with nontrivial finite normal subgroups, such as `F_2 × Z/2`.

## What remains

By Stallings's theorem, a hyperbolic group not covered above either:
- has at most one end; or
- splits nontrivially only over nontrivial finite subgroups, for example `SL_2(Z) = Z/4 *_{Z/2} Z/6`;
- or has a finite normal subgroup that is not a direct factor, for example the center of
  `SL_2(Z)`.

## Attempts

1. **2026-09-18 (lane `bh-free-23`).** The two BBMZ obstacles, re-examined.
   - (i) Finite normal subgroups: not intrinsic. Contracting RSGs can have nontrivial finite
     centers (`V_{Γ,E} × Z/2`). For direct products `H × N` with `N` finite, relabelled copies
     of the address space realize `N` faithfully. For a generating set not closed under `N`,
     even the horofunction boundary can see `N`. For example, `F_2 × Z/2` with generating set
     `{a, b, c}` has `∂_h ≅ ∂F_2 × {0,1}`, and `c` swaps the two copies.
   - (ii) Irreducible core: for free splittings `A * B`, the cut-vertex geometry of the Cayley
     graph makes the atoms behind a letter of a finite or cyclic factor into cones of a single
     type, and the tree-of-atoms argument goes through. The first case not handled is a free
     product `A * B` of two infinite freely indecomposable factors. There the atoms behind a
     `B`-letter merge with parts of `B`'s own atom tree, so no single universal type is
     available in the same way.
   - A proposal, not attempted: for a finite normal subgroup `N` that is not a direct factor,
     look for a continuous `N`-valued cocycle on the germ groupoid of `G/N ↷ ∂_h(G/N)` that
     realizes the extension. `G` would then act on `∂_h(G/N) × N` by a skew product, and the
     finite-product construction would apply to that skew product.
