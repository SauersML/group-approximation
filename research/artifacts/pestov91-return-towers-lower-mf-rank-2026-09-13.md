# Return towers lower the MF obstruction to rank two and to unit groups

2026-09-13. Written proof, not Lean-verified.

Let `X` be a nonempty finite-alphabet subshift, `F_q` a finite field,
and `R=LC(X,F_q) semidirect_T Z`, with `u f u^{-1}=f circ T^{-1}`.
Write (C) for the condition that every edge of every finite word graph
lies on a directed cycle. The earlier
[dichotomy](pestov91-subshift-lef-mf-dichotomy-2026-09-13.md) equates
(C), direct finiteness, stable finiteness and ring-LEF, and detects
failure in elementary rank at least four. Here the absence of short
periodic orbits supplies matrix coordinates inside the original ring.

## Theorem

Suppose `k>=1` and `T^j` has no fixed point for `1<=j<k`. For `n>=1`
with `nk>=4`,

`(C) iff GL_n(R) is LEF iff GL_n(R) is operator MF`.

For `n>=2` under the same inequality, the same equivalence holds for
`EL_n(R)`. In the negative case a nonzero idempotent `d` in a clopen
return corner gives `e_12(d)` in the MF radical of `EL_n(R)`. In the
unit-group case `n=1`, `k>=4`, an invisible unit is `1+d u^{-1}!=1`.

Consequently rank two suffices when `X` has no fixed points. If `X`
has no points of periods one, two or three, its unit group `R^x` is
MF exactly when it is LEF, exactly when (C) holds. This includes
every aperiodic subshift. The analytic input remains the printed
rank-four torsion-defect theorem; the new step is the return corner.

## 1. Construct a finite clopen return section

For `k=1` take `C=X`. Otherwise, zero-dimensionality and the absence
of fixed points of `T^j`, `1<=j<k`, give a finite clopen cover
`U_1,...,U_m` with `U_i intersection T^j U_i=empty` for `0<|j|<k`.
To get each neighborhood, separate a point from each of its finitely
many distinct relevant translates and shrink it finitely many times.
Starting with `C_0=empty`, set

`C_i=C_(i-1) union (U_i minus union_(|j|<k) T^j C_(i-1))`.

The new part is internally separated inside `U_i`, and removing the
old translated neighborhood excludes conflicts with the old part.
Thus every `C_i` is clopen and separated from its translates at
distances less than `k`. Every point of `U_i` is either added or lies
within fewer than `k` iterates of the old part. Hence `C=C_m` satisfies

`C intersection T^j C=empty` for `0<|j|<k`,
`X=union_(|j|<k) T^j C`.

Successive returns to `C` along every orbit therefore have gaps in
`[k,2k-1]`. A larger gap has a middle point at distance at least `k`
from every return, contradicting the covering property. Returns exist
in both directions and are uniformly bounded. Let `C_h` be the clopen
set with first return time `h`, for `k<=h<=2k-1`. The tower levels
`T^i C_h`, `0<=i<h`, partition `X`. The first-return homeomorphism is
`S(x)=T^h x` on `C_h`.

## 2. Identify the return ring and both tower corner maps

Put `p=1_C`, `P=pRp`. The return unit

`v=sum_h u^h 1_(C_h)`

has inverse `sum_h 1_(C_h) u^{-h}` and implements `S` on `LC(C,F_q)`.
It gives `P ~= LC(C,F_q) semidirect_S Z`. To check the whole corner,
partition the support of `p f u^a p` by the finite list of return
times between its two endpoints in `C`. Each resulting piece is a
coefficient times a power of `v`. The partition is finite for fixed
`a`. Distinct powers preserve the algebraic normal form, including
on periodic orbits: distinct return counts have distinct total shift
exponents at any given source point.

The return system is a finite-alphabet subshift. Record at each return
the word `x_0...x_(h-1)` and its length `h`. Concatenation reconstructs
the two-sided point with a return boundary at zero. This is a continuous
injective coding intertwining `S` with the shift; its compact image is
a subshift. In particular the existing equivalence between direct and
stable finiteness applies to `P` as well as to `R`.

For `0<=i<=2k-2` put

`D_i=union_(h>i) C_h`, `a_i=u^i 1_(D_i)`, `b_i=1_(D_i) u^{-i}`.

Disjointness of the tower levels gives

`b_i a_j=0` for `i!=j`, `b_i a_i=1_(D_i)`, `sum_i a_i b_i=1`.

Thus `r |-> (b_i r a_j)` identifies `R` with
`q M_(2k-1)(P) q`, where `q=diag(1_(D_0),...,1_(D_(2k-2)))`.
The inverse is `A |-> sum_(i,j) a_i A_ij b_j`.

If `P` were directly finite, the subshift theorem would make it stably
finite, and this matrix corner would be directly finite. Indeed a
one-sided inverse pair in a corner extends by `1-q` to one in the
full matrix ring. Therefore

`R not directly finite implies P not directly finite`. (1)

The first `k` levels give the other map. Since `D_i=C` for `i<k`,

`phi:M_k(P) -> R`, `phi(A)=sum_(i,j<k) a_i A_ij b_j`

is injective, with identity `e=sum_(i<k) a_i b_i`. Its image is a
corner subring, and `e` need not equal `1_R`. The full tower map
transfers nonfiniteness to `P`; the first `k` levels provide matrix
coordinates inside `R`.

## 3. Transfer the printed obstruction

If (C) fails, `R` and hence `P` are not directly finite. Apply the
finite-word theorem to the return subshift to find `s,t in P` with

`ts=p`, `d=p-st!=0`.

The idempotent `d` has additive order equal to the field characteristic.
The printed torsion-defect theorem kills every root with coefficient
`d` in `EL_(nk)(P)` when `nk>=4`.

Apply `phi` entrywise and add `(1-e)I_n` to embed
`GL_n(M_k(P))` into `GL_n(R)`. For `n>=2`, elementary flattening gives
`EL_(nk)(P)=EL_n(M_k(P))`: roots between outer blocks are entries of
block roots; a scalar root within one block is a commutator through
any coordinate of another block; block roots are products of their
scalar entry roots. The image thus lies in `EL_n(R)`.

The scalar root with indices `1,k+1` and coefficient `d` maps to
`e_12(d)`, since `a_0=b_0=p`. It is nontrivial, and restriction of
any MF-target homomorphism to the embedded subgroup kills it. This
proves the negative implication for both elementary and general
linear groups when `n>=2`.

For `n=1`, `k>=4`, embed `EL_k(P)` into the corner units and add
`1-e`. Its root with indices `1,2` and coefficient `d` becomes
`1+a_0 d b_1=1+d u^{-1}`, a nontrivial invisible unit. The positive
implications in all ranks follow from the existing ring-LEF models,
including inverse-entry relations to model general linear groups.
Their subgroups are LEF, and LEF implies operator MF.

## 4. The aperiodic seam already has its exact radical in units

Let `X` be the tagged seam of two infinite minimal binary systems
`Y_-,Y_+`, and work over `F_2`. Its minimal components have no periodic
points and its isolated joining orbit is free, so `X` is aperiodic.
For every `n>=2`, endpoint restriction gives

`1 -> L_n -> EL_n(R) -> EL_n(R_-) x EL_n(R_+) -> 1`,
`L_n=GL_fin(Z x {1,...,n},F_2)`.

The previous full finite-block kernel calculation works already for
two outer colors. Between colors the transvections are coefficient
matrix units; within one color they are commutators through the other.
Every invertible finite block over `F_2` has determinant one. Thus
`L_n` is the full infinite simple finitary group.

The return-corner defect `d` from section 3 vanishes at each endpoint:
the endpoint ring is stably finite, so `ts=p` in its image corner
implies `st=p`. The invisible root `e_12(d)` therefore belongs to
`L_n`. Simplicity kills all of `L_n`, and the LEF endpoint quotient
gives the reverse inclusion. Hence

`Rad_MF(EL_n(R))=L_n` for every `n>=2`.                 (2)

The kernel of `R^x -> R_-^x x R_+^x` is likewise the infinite simple
`L_1=GL_fin(Z,F_2)`. The invisible unit `1+d u^{-1}` belongs to `L_1`.
Simplicity and the LEF endpoint-unit image give

`Rad_MF(R^x)=L_1`.                                     (3)

No surjectivity for units is asserted: their maximal MF quotient is
the image of endpoint restriction.

At rank three, (2) gives precisely the original simple factors
`EL_3(R_-) x EL_3(R_+)`, without amplifying either coefficient ring.
The faithful finitary-centralizer proof gives five normal subgroups,
every proper quotient is LEF, and there are no nontrivial finite
quotients. Finite ring generation gives property (T). With payload
and phase indicators `b,p`, four torsion generators of orders `7,2,2,2`
are

`c=[[0,0,1],[1,0,1],[0,1,0]]`,
`t_b=e_12(1-b)e_13(b)`, `t_p=e_12(1-p)e_13(p)`,
`w=[[0,u,0],[u^{-1},0,0],[0,0,1]]`.

Apply the unit-idempotent decoder separately to `b` and `p`. It
supplies the roots of both idempotents and of `u,u^{-1}`, which
generate the ring and therefore the elementary group. This marking
preserves the original endpoint factors; the earlier three-element
marking of `EL_6(R)` remains a different construction.

## Scope and verification

The finite clopen construction uses no invariant measure or minimality.
The short-period hypothesis is explicit: fixed points prevent its
`k=2` separation step. The general rank-three torsion-defect problem
and the rank-three monotone example with fixed endpoints are not
settled here. The analytic input is the printed one-auxiliary-coordinate
route, not the excluded rank-transport route. This is a written proof,
not a Lean formalization, with no global priority assertion.

The [exact finite-cycle audit](check-pestov91-return-tower-matrices-2026-09-13.py)
checks the tower identities for return gaps `(2,3)`, `(3,5)` and
`(4,7)`, all 210 matrix-basis round trips, the invisible-unit formula's
coordinate placement and inverse, and 449 cyclic orders for the greedy
marker construction. It passed on MSI in 0.018254 seconds; see the
[matrix receipt](pestov91-towers-matrix-receipt-2026-09-13.json).
These are finite coordinate checks, not a proof of the infinite-system
or MF assertions.

Cairn 2.13.1 checked the six new graph nodes against snapshot
`752b5a970e7d27da9c1833bd513bd9bec4331983` in 26.555 seconds on MSI.
`check --changed` and `preview` returned zero, all three new claims
were `ESTABLISHED`, and neither baseline nor current graph had errors.
The graph had 10,313 claims and 10,574 routes. The
[Cairn receipt](pestov91-towers-cairn-receipt-2026-09-13.json) records
the source-delta and runner hashes. These validation paragraphs and
receipts were added after the run. Cairn checks dependencies, not the
validity of the mathematical proof; no Lean check was run.
