---
rg: 2
id: km-codistance-filtration-twisted-levels-are-rank-two-pairs
kind: claim
title: In the (2,4,6) twin building the only non-product levels of the codistance filtration are rank-two residue pairs twisted by one centralized reflection
artifacts:
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
distinct_from:
  km-development-has-nonzero-end-cohomology-in-degree-one: that is the open end-cohomology input; this is an established structural theorem about the Morse filtration of the twin-building product that isolates where the development's second homology could come from.
  km-lattices-admit-no-cocompact-npc-model: that shows the development is not CAT(0), closing curvature routes to contractibility; this replaces curvature by a codistance Morse filtration whose relative homology is computed residue by residue.
  triangle-colimit-rational-h2-vanishes: that computes rational cohomology of the colimit from the development's simple connectivity; this analyses the integral homology of the development itself.
---

**THEOREM (established; proof in
`km-codistance-filtration-twisted-levels-proof`).**  Let `(X_+,X_-)` be the
twin building of `Lambda=Lambda_(2,4,6)(q)`, `Z=X_+ x X_-` with the product
cell structure, `f` the minimal codistance length on residue pairs, and
`Z_(<=R)` the sublevel complexes, so `Z=union Z_(<=R)` is contractible
and the bottom level `X^ := Z_(<=0)` is the union of the closed product
cells `x x y` over opposite chamber pairs, a simply connected
four-dimensional cocompact proper `Lambda`-complex (NOT the
two-dimensional Levi-triangle development `X`, which is homotopy
equivalent to `X^` minus its mixed-type 1-skeleton; see
`km-development-has-nonzero-end-cohomology-in-degree-one`).  The opposition graphs of the thick generalized `m`-gon residues
(`m in {2,4,6}`) are connected: Abramenko--Van Maldeghem,
*Connectedness of opposite-flag geometries in Moufang polygons*
(European J. Combin. 20 (1999)), prove connectedness for every Moufang
polygon with the single exception of the `Sp_4(2)` quadrangle, far
below `q > 1764^3`.  Then:

```text
(a) Z_(<=R+1)/Z_(<=R) is a wedge, over residue pairs (R_+,R_-) of types
    (J,J')=(S-L(w),S-R(w)) at codistance w of length R+1, of the
    relative complexes (cl O_w, D), O_w the codistance-w chamber
    pairs and D the descending faces (cotype meeting L(w) or R(w)).

(b) If K=J cap wJ'w^(-1) is empty, O_w is a product of two opposition
    sets and (cl O_w, D) has homology only in degree four.

(c) Since all labels of (2,4,6) are even, the simple reflections are
    pairwise non-conjugate; hence K is empty or K={r} with
    r in J cap J' and w in C_W(r).  The latter is IMPOSSIBLE when J or
    J' has rank one: rank one forces two left (or right) descents,
    i.e. w c_0 lies in the sector opposite to c_0 at a vertex v, while
    w in C_W(r) forces w c_0 to have an edge on the wall M_r, and M_r
    never meets that sector.  So every twisted level is a pair of
    rank-two residues R_+, R_- (types among A_1 x A_1, B_2, G_2, equal
    or different) with K={r} for the unique r in J cap J' not in
    {the two descents}.

(d) At a twisted level, with phi the co-projection bijection between
    the r-panels P_+^1 <= R_+, P_-^1 <= R_-: the chambers of R_+
    involved are those opposite to some chamber of P_+^1 (each is
    opposite to q of the q+1 and projects to the last one), giving
    classes A_1..A_(q+1) of R_+ and B_1..B_(q+1) of R_-, and

        O_w = union_(i != j) A_i x B_j.

    In the link graphs, one vertex type is single-class and the other
    meets every class once (no triangles / girth), so with
    A = union A_i, B = union B_j (connected bipartite graphs) the
    relative complex is the reduced suspension of

        Omega = (A * B) minus the open stars of the matched-class
                single-class-vertex edges,

    and H_k(cl O_w, D) = H~_(k-1)(Omega).  In particular
    H_1 = H_2 = 0 of the relative complex, and

        H_3(cl O_w, D) = H~_2(Omega)
          = coker( H_1(A) (x) H_1(B) -> (+)_(matched (p',p'')) Z_1(K_(q,q)) ),

    the map sending a product of graph cycles to its local
    rank-one data at each matched vertex pair.
```

**Consequences.**  `H_1(X^)=H_2(X^)=0`, i.e. the thick part `X^` is
2-connected and `Lambda` is of type `F_3` by Brown's criterion, iff the
cokernel in `(d)` vanishes for every twisted type.  For the grid type
`A_1 x A_1` it vanishes (computed in
`km-development-has-nonzero-end-cohomology-in-degree-one`, attempts).
The remaining finite statement is
`km-twisted-level-product-cycles-surject`.  If it holds, then
`H^2(Lambda;Z Lambda)=H^2_c(X^)` by universal coefficients, and
Corollary D of Ioana--Spaas--Wiersma fires iff `H^2_c(X^)!=0`.  The
development `X` itself is never contractible: it contains embedded
2-spheres (two cone discs over a link cycle glued along their far-edge
circle; same node), so no point-class argument is available.

**Why the affine case is different.**  For `A~_2` all labels are odd,
the simple reflections are conjugate, and rank-`(1,2)` twisted levels
DO occur; there the relative complex is `B cup union_i Cone(Opp(y_i))`
over an `s`-panel `{y_i}` and carries the nonzero class `(z,-z)` for
any cycle `z` opposite to two chambers of the panel, consistent with
`SL_3(F_q[t,t^(-1)])` having finiteness length three
(Bux--Köhl--Witzel), so that its thick part `X^` cannot be 3-connected.
The even labels of compact hyperbolic type remove exactly these levels
from the filtration (they survive only inside `X^` itself, as links of
mixed edges, where they produce the 2-spheres of the development).
