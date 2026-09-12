# Centralizer homotopies identify the ordinary singleton fibre uniformly

Date: 2026-08-11

## Outcome

Let `G=SL_3(Z)` and let `M_p=F_2[P^2(F_p)]` be the projective coefficient
module for an odd prime `p`.  The first positive vertex-resolution generator
has the singleton locus

`P(V_+) disjointUnion P(V_-)=P^0(F_p) disjointUnion P^1(F_p)`             `(SCO1)`

from `TRUE_PROJECTIVE_SINGLETON_EIGENSPACE.md`.

All singleton cycles indexed by `P(V_-)` represent the same class in
`H_2(G;M_p)`.  More quantitatively, there is a fixed finite set of integral
chain-homotopy templates, independent of `p`, whose specializations give a
bounded-support relation along every edge of a connected Schreier graph on
`P(V_-)`.

Thus the all-prime singleton quotient has rank at most two:

`{exceptional point} disjointUnion {ordinary projective line}
       -> span_F2(exceptional_class,ordinary_class)`.                    `(SCO2)`

The two displayed classes may conceivably coincide at a level; that only
reduces the primary correction.  The theorem needed for uniformity is the
upper bound and the orbitwise identification.

This closes the **algebraic** part of the two-fibre pattern.  It does not by
itself give a uniformly bounded integral `L2` section for all parity demands.
A real spectral gap gives a bounded real flow, whereas rounding it to an
integral mod-two flow is exactly the arithmetic issue that must not be
silently discarded.

## 1. The integral centralizer

The involution is

`T=[[0,1,1],[1,0,1],[0,0,-1]]`.                                  `(SCO3)`

For the row action, choose the integral eigenbasis

`u=(1,1,1)`, `v=(1,-1,0)`, `w=(0,0,1)`.                           `(SCO4)`

The basis matrix has determinant of absolute value two.  Let
`Gamma(2)=ker(SL_2(Z)->SL_2(F_2))`.  For `A in Gamma(2)`, act as the identity
on `u` and by `A` on `span(v,w)`.  Since `A=1 mod 2`, this block action
preserves the index-two overlattice `Z^3`; it therefore gives an integral
matrix

`iota(A) in SL_3(Z)` with `iota(A)T=T iota(A)`.                    `(SCO5)`

For every odd `p`, reduction maps `Gamma(2)` onto `SL_2(F_p)`.  Indeed the
Chinese remainder theorem gives

`SL_2(Z/2p) ~= SL_2(F_2) x SL_2(F_p)`,                            `(SCO6)`

and the standard reduction map from `SL_2(Z)` is onto; choose the component
`(1,A_p)`.  Consequently the image of the integral centralizer acts
transitively on

`P(V_-)=P^1(F_p)`.                                                `(SCO7)`

Fix once and for all a finite symmetric generating set `S` of `Gamma(2)`.
The specialized Schreier graph of `S` on `P(V_-)` is connected for every
odd `p`.

## 2. Inner automorphisms give the required homology relations

We record the standard functorial argument because it is the point at which
an illegitimate coefficient translation could otherwise enter.

For `c=iota(A)` in the centralizer, let

`phi_c(g)=c g c^(-1)`,
`f_c(m)=m c^(-1)`.                                                `(SCO8)`

For the right `G`-module `M_p`, these maps are compatible:

`f_c(mg)=mgc^(-1)=f_c(m) phi_c(g)`.                               `(SCO9)`

They therefore induce a chain map on the normalized bar resolution computing
`H_*(G;M_p)`.  The singleton class has the concrete bar representative

`z_x=x tensor [T|T]`.                                             `(SCO10a)`

Indeed `xT=x`, `T^2=1`, and characteristic two make its bar boundary zero.
Since `c` centralizes `T`, the map `(phi_c,f_c)` sends `(SCO10a)` exactly to
`z_(x c^(-1))`.  Since `phi_c` is inner, the induced bar chain map is chain
homotopic to the identity.  The chain homotopy therefore gives

`z_(x c^(-1))-z_x in im(partial_3)`.                               `(SCO10)`

This is the justified replacement for the false assertion that arbitrary
coefficient translations commute with one fixed HAP differential.  Both the
group and coefficient module are transported as the compatible pair
`(phi_c,f_c)`.

Apply `(SCO10)` to the fixed generators `c in iota(S)`.  Connectivity from
`(SCO7)` proves that all ordinary singleton classes agree, establishing
`(SCO2)`.

## 3. Uniform support of the edge fillings

Choose fixed chain comparisons through degree three between the bar cycles
appearing above and HAP's finite free resolution, and choose the standard
inner bar homotopy for each member of the finite set `iota(S)`.  Only
finitely many fixed bar chains occur, so their images are finite sums in the
finite-rank HAP modules.  Let `C_S` be the maximum number and absolute
coefficient sum of their group-ring terms.

After specialization to any finite projective action, every group element
becomes a permutation matrix.  Hence each edge relation `(SCO10)` has a
degree-three filling with support and operator norm bounded only by `C_S`,
independently of `p`.  This is an existence theorem for finitely many fixed
Wall-compatible relation templates.  The explicit four-term identity in
`TRUE_PROJECTIVE_DERIVED_E1_AUDIT.md` is one particularly small instance.

The congruence Schreier graphs also have a uniform **real** spectral gap by
the classical congruence property-`tau` theorem for `SL_2(Z)` (equivalently,
Selberg's gap, inherited by finite-index `Gamma(2)` and by Schreier
quotients).  Therefore the real incidence maps possess uniformly bounded
`L2` pseudoinverses.

## 4. Exact remaining arithmetic gate

The last sentence is not an integral decoder.  A sparse parity demand can
require an integral path even when its optimal real electrical flow has
bounded norm.  What remains is precisely one of the following equivalent
forms for this fixed family of chain templates:

1. construct a uniformly bounded integral section after coupling the edge
   relations to the other Wall generators;
2. prove directly that the paired discriminant lattice of this ordinary
   fibre has uniformly bounded repair constant;
3. show that the additional higher-support relations turn the parity code
   into bounded-diameter filling geometry.

Thus no growing homology rank, orbit classification, or real spectral gap
remains in this singleton sector.  Its only unresolved content is the
circle/integral rounding step already isolated by the global TRUE program.
