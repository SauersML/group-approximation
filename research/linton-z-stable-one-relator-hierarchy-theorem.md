---
rg: 2
id: linton-z-stable-one-relator-hierarchy-theorem
kind: claim
title: Linton's criterion — a Z-stable one-relator hierarchy without Baumslag–Solitar subgroups gives a hyperbolic virtually special group, detected by the graph of cyclic stabilisers
distinct_from:
  groups-with-staggered-presentations-are-coherent: that is coherence of staggered presentations (Jaikin-Zapirain–Linton); this is Linton's hyperbolicity and virtual specialness criterion for one-relator hierarchies.
  linton-rational-derived-series-theorem: that is Linton's rational-derived-series structure theorem; this is the Z-stable hierarchy criterion from a different paper, arXiv:2202.11324.
artifacts:
  - research/artifacts/one-relator-magnus-row29-2026-09-13.md
---

**Import (M. Linton, *One-relator hierarchies*, arXiv:2202.11324v3, 27 Jun 2024;
Duke Math. J. 174 (2025)).** Statements read from the arXiv PDF, with page numbers.

**Z-stable number (p. 3, restated p. 23).** For an isomorphism `psi : A -> B` between
subgroups of `H`, inductively define `A_0^psi = {[H]}` and
`A_(i+1)^psi = {[psi(A cap A_i)]}` over `[A_i] in Abar_i^psi`, where `Abar_i^psi` is the
subset of non-cyclic classes. Then `sZ(psi) = sup{k+1 | Abar_k^psi != empty}`, and
`H *_psi` is Z-stable if `sZ(psi) < infinity`.

**Definition 1.1 (p. 3).** "A one-relator hierarchy `X_N -> ... -> X_1 -> X_0 = X` is a
Z-stable hierarchy if `sZ(psi_i) < infinity` for all `i < N`."

**Remark 6.2 (p. 24).** "If H is a one-relator group with the trivial relation, H itself is
a Magnus subgroup of H. Thus, HNN-extensions of free groups with finitely generated
strongly inert edge groups are inertial one-relator extensions."

**Lemma 6.13 (p. 29).** "Let `H *_psi` be an inertial one-relator extension with H hyperbolic
and with both edge groups quasi-convex in H. Then the graph of cyclic stabilisers G is
locally finite. Moreover, if `sZ(psi) < infinity`, then `G = G_(sZ(psi))` is finite."

**Theorem 6.14 (p. 29).** "Let `H *_psi` be an inertial one-relator extension. Suppose that
`sZ(psi) < infinity`, that H is hyperbolic and that A and B are quasi-convex in H. The
following are equivalent: (1) G acts acylindrically on T. (2) G does not contain any
Baumslag–Solitar subgroups. (3) `pi_1(G)` admits no cyclically alternating and cyclically
reduced word."

**Theorem 7.1 (pp. 3, 31).** "Let X be a one-relator complex and
`X_N -> ... -> X_1 -> X_0 = X` a one-relator hierarchy. The following are equivalent:
(1) [it] is a quasi-convex hierarchy and `pi_1(X)` is hyperbolic. (2) [it] is an
acylindrical hierarchy. (3) [it] is a Z-stable hierarchy and `pi_1(X)` contains no
Baumslag–Solitar subgroups. Moreover, if any of the above is satisfied, then `pi_1(X)` is
virtually special and the image of `pi_1(A)` in `pi_1(X)` is quasi-convex for any connected
subcomplex `A in X_i`."

**Length-one hierarchies ending in a free group (Example 6.12, p. 28).** "This one-relator
splitting is also a one-relator hierarchy of length one as `y^2zxz^-1yzxz^-1` is a primitive
element of `F(x,y,z)`." Example 1.2 (p. 4) treats the same shape.

**Graph of cyclic stabilisers (p. 27).** Its vertices are the classes `[<a>]_A` of maximal
cyclic subgroups of A (resp. B) that contain `A cap Stab(S)` (resp. `B cap Stab(S)`) for a
geodesic segment S of the Bass–Serre tree with an endpoint at H. Its edges are H-edges
(`h in H`) and t-edges (`h in A t^-1 B u B t A`), one for each double coset
`<nu(v)> h <nu(w)>` with `<nu(v)> cap <nu(w)>^h != 1`. When `v, w` are both in the A-part or
both in the B-part, `h` is required to lie outside `<nu(v)><nu(w)>`. A path is alternating if it
never traverses two H-edges or two t-edges in a row.
