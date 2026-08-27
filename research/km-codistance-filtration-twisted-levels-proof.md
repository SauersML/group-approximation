---
rg: 2
id: km-codistance-filtration-twisted-levels-proof
kind: route
title: Descent sets, Kilmoyer intersections, twin co-projections, and the wall geometry of the triangle group
target: km-codistance-filtration-twisted-levels-are-rank-two-pairs
requires: []
---

**(a) Levels.**  `f` is constant on open cells and monotone on faces,
so `Z_(<=R)` is a subcomplex.  A face `(R_J(x),R_J'(y))` of a chamber
pair at codistance `w` has level `min length(W_J w W_J')`, because the
codistances realized in a residue pair fill the double coset's minimum
(twin axiom Tw2 shortens along every other chamber of a panel).  The
face is descending iff `w` is not `(J,J')`-reduced iff
`J cap L(w) != emptyset` or `J' cap R(w) != emptyset`.  Level-`(R+1)`
faces of a cell lie in the same residue pair `(R_(S-L)(x),R_(S-R)(y))`,
so the quotient splits as a wedge over residue pairs.

**(b) Product levels.**  Gate property of twin co-projections: for
`y'' in R_-`, `delta^*(x'',y'') = delta^*(x'',proj(x'')) delta(proj(x''),y'')`
with `proj(x'')` the chamber of `R_-` at longest codistance; the
longest codistance from `x''` to `R_-` is the longest element of the
coset `delta^*(x'',y)W_J'`.  Writing `delta^*(x'',y)=delta(x'',x_1) w_(0,J) w`
with `x_1=proj_(R_+)(y)`, the pairs at codistance exactly `w` are those
with `delta(x_1,x'') in w_(0,J) W_K` and `y''` opposite `proj(x'')`, and
`proj(R_+)` is the `K`-residue of `proj(x)`.  For `K` empty the
co-projection is constant, `O_w=Opp(x_1) x Opp(y_1)`, and the relative
complex is the smash product of the two one-sided relative complexes,
each the (iterated) suspension of an opposition set: for a rank-one
residue, `q` discs on a common circle; for a rank-two residue, the
suspension of the opposition subgraph of the link polygon, a wedge of
2-spheres when that graph is connected.  Smash of wedges of 2-spheres is
a wedge of 4-spheres.

**(c) Which `K` occur.**  `K` consists of simple reflections of `J` that
are `w`-conjugate into `J'`; even labels make each simple reflection
the only one in its conjugacy class (the conjugacy classes of simple
reflections are the connected components of the odd-label graph), so
`K <= J cap J'` and `wrw^(-1)=r` for `r in K`.  A rank-two `K=J` would
make `w` centralize a finite rank-two parabolic, i.e. fix the vertex it
fixes, so `w in W_J`, contradicting reducedness; hence `|K|<=1`.  If `J`
has rank one, `L(w)` has two elements `t,u`, so `w c_0` is separated
from `c_0` by both walls `M_t, M_u` through the vertex `v_(tu)`, i.e.
lies in the closed sector opposite to `c_0` at `v_(tu)`.  But `w` fixes
the wall `M_s` (`s` the third reflection), so `w c_0` has an edge on
`M_s`.  The geodesic `M_s` meets `M_t` and `M_u` only at the other two
vertices of `c_0`, which lie on the rays bounding the `c_0`-sector; it
is therefore disjoint from the rays bounding the opposite sector and
from that sector, so no chamber with an edge on `M_s` lies there.  The
same argument with `w^(-1)` handles rank-one `J'`.

**(d) Twisted levels.**  With `K={r}`, `w_(0,J)` central (even `m`),
the allowed `x''` have `delta(x_1,x'') in {w_0, w_0 r}`: opposite to `x_1`
or to the `r`-neighbours of `x_1`, i.e. opposite to exactly `q` of the
`q+1` chambers of the panel `P_r(x_1)` and projecting to the remaining
one; the co-projection of `x''` into `R_-` is the `phi`-image of that
projection, so `y''` is admissible iff it is opposite to `phi(proj
x'')`, iff its own projection to `P_r(y_1)` is not `phi(proj x'')`.
This is `O_w = union_(i!=j) A_i x B_j`.  Single-class vertices: for a
panel of flags through a line `ell_1`, the points off `ell_1` project to
a unique point of `ell_1` (GQ: unique collinear point; GH: unique point
at distance four; grid: the point itself), while each line far from
`ell_1` meets every class exactly once (a repeated class would close a
cycle shorter than the girth); dually for panels through a point.  Thus
the simplices of `A*B` absent from `Omega` are exactly those containing a
matched-class pair of single-class vertices, i.e. the open stars of
those edges, which are pairwise disjoint.  The identification of the
level complex with the reduced suspension of `Omega` is the usual cone
structure on the link (cells containing the central vertex `v`
correspond to cone cells over link simplices, with the descending faces
being those missing `v`).  Mayer--Vietoris for deleting disjoint open
edge stars, with `Lk(p'*p'')=Lk_A(p')*Lk_B(p'')=K_(q,q)` (each
single-class vertex has exactly `q` neighbours in its opposition graph),
gives `H~_1(Omega)=0` and the cokernel formula for `H~_2(Omega)`, using
`H~_2(A*B)=0` and `H~_3(A*B)=H_1(A)(x)H_1(B)` for connected graphs.
