---
rg: 2
id: km-development-has-nonzero-end-cohomology-in-degree-one
kind: claim
title: The Levi-triangle development of a simple Kazhdan Kac-Moody lattice has nonzero degree-one end cohomology
artifacts:
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
distinct_from:
  compact-hyperbolic-km-lattices-fail-lp: that is the C*-algebraic LP conclusion; this is the single topological input, `H^1_infty(X;Z)!=0` for the development `X`, which by `km-group-ring-h2-is-development-end-cohomology` is literally `H^2(Lambda,Z Lambda)!=0`.
  km-lattices-admit-no-cocompact-npc-model: that shows the development is not CAT(0), so neither contractibility nor visual-boundary methods are available; this asks a weaker question about the development, which does not require contractibility and is insensitive to `H_2(X)` except through the pairing with compactly supported classes.
---

**OPEN.**  Let `Lambda=Lambda_(2,4,6)(q)`, `q>1764^3`, with its
Abramenko--Mühlherr triangle of finite rank-`<=2` Levi subgroups, and let
`X` be the development (the opposition complex of the twin building:
vertices are opposite pairs of rank-two residues, edges opposite pairs
of rank-one residues, two-cells opposite pairs of chambers, cf.
`km-lattices-admit-no-cocompact-npc-model`).  Prove

```text
H^1_infty(X;Z) = ker( H^2_c(X;Z) -> H^2(X;Z) ) != 0.             (DE1)
```

Equivalently (`km-group-ring-h2-is-development-end-cohomology`):
exhibit a compactly supported integral 2-cochain on `X` that vanishes on
every finite 2-cycle of `X` but is not the coboundary of a compactly
supported 1-cochain.

## Attempts

- **Retract route.**  A twin apartment `Sigma=(Sigma_+,Sigma_-)` gives
  an embedded copy of the `(2,4,6)` hyperbolic tessellation inside `X`
  (the pairs `(sigma, op(sigma))`), a properly embedded plane with
  `H_2=0` and `H^2_c=Z`.  A PROPER cellular retraction `X -> Sigma`
  would prove `(DE1)` by the retract criterion.  The obvious candidates
  fail properness: composing the projection to one factor with the
  building retraction, or with the co-retraction centered at a chamber
  of the other half, has infinite fibers, because the set of chambers
  opposite a fixed chamber of a twin building is infinite.
- **No proper map through the product detects the apartment.**  If
  `f: X -> H^2` is proper and factors through a proper map
  `X_+ x X_- -> H^2`, then `f` has degree zero on every apartment: the
  circle at infinity of the plane bounds a disc in the boundary
  `S^1 * S^1 = S^3` of the product.  A proper degree-nonzero map must
  use the intrinsic geometry of the opposition complex.
- **Structure of the development.**  Every opposite chamber pair lies
  in exactly one twin apartment, so every 2-cell of `X` lies in exactly
  one planar subcomplex; `X` is a union of hyperbolic planes, any two
  meeting only in wall segments (an opposite panel pair shared by two
  twin apartments must lie on a wall, by the uniqueness of the opposite
  of a chamber inside its own twin apartment).  Each edge lies in
  `q(q+1)` planes.  No 2-cycle is supported in a vertex star.
- **`H_2(X) != 0`: explicit embedded 2-spheres (2026-08-23).**  Fix a
  vertex `v` of `X_+` of cotype `{t,u}`, an `s`-panel `e'` of `X_-`
  with chambers `y_1,...,y_(q+1)`, and let `x_1 = proj_(R(v))(y_i)`
  be the twin co-projection, which is the same chamber for all but one
  chamber of the panel (lengthening `w_(0,{t,u})` by `s` happens at
  exactly one chamber of the panel).  For two such generic `y_i,y_j`
  the chambers through `v` opposite to `y_i` and to `y_j` coincide:
  the opposition subgraph `Opp(x_1)` of the link polygon of `v`, a graph
  with cycles for `q>=2`.  For a cycle `z` in it,

      `S_z = sum_(x in z) eps_x [ (x,y_i) - (x,y_j) ]`

  is a 2-cycle of `X`: the edges at `v` cancel along `z`, and the far
  edges `(e_s(x), e_s(y_i)) = (e_s(x), e') = (e_s(x), e_s(y_j))` cancel
  between the two terms because `e'` is the `s`-panel of both chambers.
  Geometrically `S_z` is two discs -- fans around the distinct vertices
  `(v, v_(tu)(y_i))` and `(v, v_(tu)(y_j))` of `X` -- glued along the
  common boundary circle `sum eps_x (e_s(x), e')`.  Since `X` has no
  3-cells, `[S_z] != 0`.  Hence the development is NEVER contractible
  (for any thick 2-spherical rank-three twin building), the point class
  of a 2-cell is NOT in `H^1_infty(X)` (it pairs to `±1` with any `S_z`
  through it, and `Lambda` is transitive on 2-cells), and `(DE1)` asks
  for a compactly supported 2-cochain orthogonal to all the spheres
  `S_z` and to every other 2-cycle, with nonzero class in `H^2_c(X)`.
  The earlier "contractible iff `F_infty`" remark is therefore moot for
  `X` itself; `F_infty` would need a different model.
- **Codistance filtration and the product model.**  Inside the
  contractible product `Z=X_+ x X_-` (product cell structure) the
  sublevel complexes `Z_(<=R)` of bounded minimal codistance are
  `Lambda`-cocompact and increase to `Z`.  The bottom level
  `X^ := Z_(<=0) = union of the closed 4-cells x x y over opposite
  chamber pairs` is NOT the development: `X` is homotopy equivalent to
  `X^` minus the mixed-type 1-skeleton `Y_1` (cells `(v,v')`, `(v,e')`,
  `(e,v')` of disjoint types), via the poset retraction
  `(sigma_+,sigma_-) -> (sigma_+^tau, sigma_-^tau)`, `tau` the common
  type, on the pairs with overlapping types.  The mixed-vertex links
  of `X^` are twisted join complexes of opposition type (codistance
  one, `K = J cap J'` a single reflection) and the mixed-edge links are
  `union_i Opp(y_i) cup union_i Cone(Opp(y_i))` over a panel, whose
  `H~_2 = ker((+)_i H_1(Opp(y_i)) -> H_1(union_i Opp(y_i))) != 0`
  carries exactly the classes `(z,-z)` that become the spheres `S_z`
  under `X^ minus Y_1 ~ X`.  `X^` is simply connected (van Kampen over
  the neighbourhood of `Y_1`, all links connected, `X` simply connected).
  The relative homology of the filtration is computed in
  `km-codistance-filtration-twisted-levels-are-rank-two-pairs`; under the
  finite input `km-twisted-level-product-cycles-surject` it gives
  `H_1(X^) = H_2(X^) = 0`, so `X^` is 2-connected, `Lambda` is of type
  `F_3`, and `H^2(Lambda;Z Lambda) = H^2_c(X^)` (universal coefficients
  with `H_1(X^)=H_2(X^)=0`).  Corollary D then fires iff
  `H^2_c(X^) != 0`, i.e. iff the 4-dimensional 2-connected thick part
  has a compactly supported 2-class; by the sequence of the closed
  subspace `Z_(<=0) <= Z` and `H^2_c(Z)=H^3_c(Z)=0` (Künneth with the
  top-degree concentration of the buildings), `H^2_c(X^) = H^3_c(Z
  minus X^)`, the compactly supported cohomology of the cusp region of
  pairs at positive codistance length.  This is the Borel--Serre-type
  question for the twin-building thick part; it is open here.
- **Thick-part models and quasi-isometry.**  All `Z_(<=R)` are
  quasi-isometric to `Lambda`; by Gersten's invariance of
  `H^2(Lambda;Z Lambda)` for finitely presented groups the end
  cohomology `H^1_infty(Z_(<=R))` is independent of `R` once `Z_(<=R)`
  is simply connected, while `H^1_infty(Z)=0`.  `(DE1)` is the failure
  of this vanishing to persist under truncation to bounded codistance.
- **Heuristic tension.**  For the affine analogue
  `SL_3(F_q[t,t^(-1)])` the finiteness length is three
  (Bux--Köhl--Witzel), and for the one-place group `SL_3(F_q[t])`
  (finiteness length one, property (T)) the group-ring `H^2` is
  expected nonzero from the rational Tits building at the cusp.  No
  analogous computation is recorded for two places or for
  compact-hyperbolic type; both `H^2(Lambda;Z Lambda)=0` and `!=0`
  remain consistent with what is established.
- **Status after the same-day refutation of the surjectivity
  (2026-08-23, final).**  The twisted surjectivity holds at grid and
  `B_2` levels (large `q` prime to six) but FAILS at every `G_2` level:
  the one-class-deleted opposition geometry of the hexagon is
  disconnected (computed at `q = 2, 3`) and component-indicator
  annihilators give nonzero cokernel, hence nonzero relative `H_3` at
  every hexagon level of the codistance filtration.  The earlier
  same-day note deriving `H^2(Lambda;Z Lambda) = 0` from full
  surjectivity is therefore MOOT: this claim is OPEN again, and the
  explicit hexagon-level classes are candidate sources for its truth
  through the connecting maps of the filtration -- the sharpest
  remaining objects on both sides of the LP fork.
