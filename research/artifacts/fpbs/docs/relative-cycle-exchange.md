# Relative cycle exchange: what descends, and what must remain connected

September 10, 2026. Written deductions over the previously imported measured
L2 identity and the cited spanning-forest theorems. Neither Fixed Price nor
Benjamini--Schramm is resolved. No mathematical priority is claimed.

## 1. The relative operator descends exactly

Let pi:(Y,nu)->(X,mu) be an equivariant probability-preserving factor of
essentially free p.m.p. actions of an infinite countable group Gamma. Work
on invariant conull sets where both actions are free. Let H be a simple,
bounded-degree graphing generating the orbit relation on X. Suppose Phi
is a measurable generating subgraphing of pi*H on Y.

Freeness identifies each Y-orbit bijectively with its X-orbit. In the
common edge Hilbert space of that orbit, let P_H be the projection onto
the closed span Z(H) of finite cycle chains, and let P_Phi be the
projection onto Z(Phi), extended by zero to the ambient edge space.
Use an orientation chosen on the base and inherited upstairs. Since
Z(Phi) is a closed subspace of Z(pi*H),

    Q_y = P_H - P_Phi,y

is an orthogonal projection, with 0 <= Q_y <= P_H. The graphing
cost--Betti identity and the equality of the group Betti numbers give

    Tr_Y(Q) = z(pi*H)-z(Phi) = c(H)-c(Phi).                 (1)

Here both graphings generate their full orbit relations. Dropping that
hypothesis would invalidate the cancellation of the Betti terms.

Disintegrate nu = integral nu_x dmu(x). Define, in the weak operator sense,

    K_x = integral Q_y dnu_x(y).                            (2)

This is a base-measurable equivariant positive contraction, and

    0 <= K_x <= P_H,x,
    Tr_X(K) = c(H)-c(Phi).                                 (3)

For completeness, enumerate the countable orbit edges measurably. Each
matrix coefficient of Q_y is bounded and measurable. Integrating these
coefficients defines, on the countable dense set of finite rational
linear combinations of edge vectors, a positive sesquilinear form bounded
by that of P_H. It therefore extends uniquely to the asserted bounded
operator. The disintegrations can be chosen equivariant simultaneously
for all group elements: uniqueness of disintegration gives equivariance
for each element, and Gamma is countable. Thus the integrated operators
are consistent under changing the orbit root.

The normalized trace of an equivariant edge operator A is

    Tr_X(A) = (1/2) integral_X sum_{e incident to x}
                         <A_x delta_e,delta_e> dmu(x).

Bounded degree makes this finite. Apply Fubini to its diagonal entries
to obtain Tr_X(K)=Tr_Y(Q), proving (3). In particular Tr_X(I)=c(H).
The trace in (3) is generally not the dimension of a subspace, since K
need not be a projection.

This is a relative statement. It does not set either action's possible
cost--Betti excess to zero. It transports exactly the excess of the
specified ambient graphing over the specified source graphing.

### Availability of an ambient graphing

If Phi uses only finitely many group labels, retain a base edge in H
when its conditional probability of belonging to Phi is positive. This
gives a bounded-degree measurable H. The probability that a source edge
is present while its conditional probability is zero is zero. Remove
the countable orbit saturation of those null sets. Then Phi is contained
in pi*H throughout almost every orbit. Its generating paths project to
H-paths, so H generates the base relation. Deduplicate unoriented edges
before taking costs or cycle spaces.

Finite-label generating graphings approximate cost for finitely
generated groups: truncate a near-optimal graphing split into group
labels, then add each fixed generator only on the set where its
endpoints are not yet connected. These exceptional measures tend to
zero because each required path in the original graphing is finite.
Consequently the setup applies arbitrarily near the source cost in the
existing finitely generated comparison problem.

## 2. Determinantal deletion fails for an actual relative certificate

It is tempting to sample deleted edges with determinantal kernel K.
Their expected edge measure is Tr(K), exactly the desired saving.
This rule does not, however, preserve connectivity, even when K comes
from a connected source treeing as in Section 1.

Choose an even integer 2r sufficiently large and an integer M>(2r)^(5/2).
Theorem 1.1 of Pete--Timar, with d=2, implies that the free uniform
spanning forest of

    G = T_(2r) x C_M

has infinitely many components almost surely. Take M>=3. This is the
product Cayley graph of Gamma=F_r x (Z/MZ), with free generators
a_1,...,a_r and cyclic generator t.

Let X be a nontrivial Bernoulli action of Gamma, and let
Y=X x (Z/MZ) with uniform second coordinate. The free generators act
trivially on that coordinate and t adds one. The projection to X is a
free p.m.p. factor. Let H be the full product Cayley graphing on X.
On Y retain:

* each a_i-edge whose starting point has second coordinate zero;
* each positive t-edge except those whose starting point has second
  coordinate M-1.

Inside every cyclic fiber the retained edges form the path
0--1--...--(M-1). Between each adjacent pair of cyclic fibers there is
exactly one retained horizontal edge, at coordinate zero. Contracting
the fiber paths gives T_(2r). The retained graph Phi is therefore a
connected spanning tree on each orbit. Its cost is

    c(Phi) = (M-1)/M + r/M = 1+(r-1)/M.                    (4)

Every ambient edge has positive conditional retention probability, so H
is also precisely the conditional-support graphing in Section 1.
Since Phi has no finite cycles, P_Phi=0. Thus

    Q = K = P_H,
    Tr(K) = (r+1)-[1+(r-1)/M].                             (5)

Deleting the determinantal process with kernel P_H retains its
complement, whose kernel is I-P_H. By the transfer-current description
this is exactly the free uniform spanning forest of G. It is
disconnected almost surely by the choice of r and M.

This counterexample survives all of the following additional hypotheses:
the base is Bernoulli; the extension has finite fibers; the source
graphing generates and is a treeing; K is already a projection; K has
the exact relative trace; and the ambient graphing is conditional
support. The failure does not arise from averaging a projection into
a nonprojection. In this example averaging changes nothing at all.

We assert failure of this particular determinantal law. We do not
assert failure of every measurable rounding rule, or any positive
lower bound on the cost of repairing its components. Nor is an
invariant random law automatically realizable inside the prescribed
base action. The connectivity failure already occurs at the level of
the law, before that separate realization issue.

## 3. A successful exchange keeps finite blocks connected

The same example has an exact construction on every free p.m.p. action
of Gamma, without the added finite coordinate. This is a reconstruction
of a known fixed-price family, useful for identifying the missing
geometric data rather than for claiming a new case of Fixed Price.

Partition the base into the M-point orbits B of the finite cyclic
subgroup. Choose a Borel representative rho(B) in each such finite
orbit. In B retain the path

    rho(B), t rho(B), ..., t^(M-1) rho(B).

For every i and every block B, retain the single ambient edge

    {rho(B), a_i rho(B)}

between B and a_i B. The action of F_r on the block quotient is free:
if w B=B, then w x=t^j x for some x and j, whence freeness of the
Gamma-action implies w=t^j and therefore w=1. Its Cayley graph is a
tree. Thus the retained graph is connected and acyclic, just as in
Section 2, even though the representative choices vary between blocks.

For the cost calculation, the representative set A has measure 1/M:
its M cyclic translates partition the space and the action preserves
measure. The internal paths contribute (M-1)/M. The restrictions of
the a_i to A contribute r/M, with no duplicate unoriented edges.
The result again has cost 1+(r-1)/M. Since a generating treeing attains
relation cost, this is optimal.

The hidden global phase has been replaced by independently allowable
choices of representatives of finite blocks. Those choices fit
together because the block quotient is a tree. No coherence between
representatives of different blocks is needed. In contrast, the cycle
projection in (5) contains none of these choices: it is identical for
every source spanning tree in this ambient graph.

## 4. The next exchange question, with an actual repair bill

For a base edge set D to delete and a graphing A of edges to add, put

    J = (H minus D) union A.

If J generates, then

    c(J) <= c(H)-m_H(D)+c(A).

To match the source graphing up to eta>0, it suffices to construct such
D,A on the base with

    m_H(D)-c(A) >= Tr(K)-eta.                               (6)

The expression c(A) must charge the actual added graphing; a count of
cycle dimensions or a count of disconnected components cannot replace
it. Paths witnessing generation may be long. Section 3 satisfies (6)
with A empty by constructing connected finite blocks and one bridge
per quotient edge.

There is presently no proof of (6) for general factors. Allowing
arbitrary added orbit edges makes it another exact formulation of the
cost comparison, not an independently easier theorem. Requiring no
added edges would be a stronger constrained-subgraph assertion, which
we also have not proved. The useful research target is a construction
of blocks and exchanges with a controlled repair bill that does not
require a finite normal subgroup or a tree quotient. The operator
identity supplies the target amount; it does not supply that
construction. No new open Cairn premise is introduced merely to
rename the existing comparison.

## Sources and certificate boundary

Repository reconnaissance covered the existing cycle-dimension identity,
short-cycle surgery, reuse compression, and the recorded FUSF
disconnection obstruction. The specific relative operator construction
and its finite-extension counterexample were checked against those
artifacts on September 10, 2026.

* [Lyons, Determinantal probability measures](https://arxiv.org/pdf/math/0204325),
  Section 3 (printed page 10): the free spanning forest has kernel the
  orthogonal complement of the closed finite-cycle space. Section 8
  gives determinantal measures for positive contractions and the
  complementary-kernel identity. These are imported probability facts.
* [Pete--Timar, The Free Uniform Spanning Forest is disconnected in some
  virtually free groups, depending on the generator set](https://real.mtak.hu/162288/2/2006_06387v2.pdf),
  Theorem 1.1: for each d, all sufficiently large k and every connected
  finite d-regular transitive H with more than k^(5/2) vertices give
  disconnected FUSF on T_k x H. Only this stated theorem is imported
  for Section 2.
* The group/action Betti equality and graphing dimension identity are
  the imports recorded in `cost-cycle-structure.md`, Sections 1 and 3.
  Optimality of treeings is the classical Gaboriau theorem, also
  recorded in the existing cost artifacts.
* The general problem remains open in our work; its current literature
  status was rechecked September 10 against the references in
  `fpbs-fixed-price-universal`, including the July 2026
  [product-neighbourhood preprint](https://arxiv.org/html/2607.20273v1).

The proofs here are written mathematics, not Lean verification. Cairn
compilation checks their dependency registration and explicit open
boundary. No finite numerical experiment certifies a universal claim.
