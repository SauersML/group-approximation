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

## 5. A common finite-block forest can be imposed at no infimum cost

The finite normal subgroup in Section 3 is not needed to create a common
collection of connected blocks. What it supplied there was an explicitly
solvable quotient. The following normal form separates these two issues.

Let R be an aperiodic countable p.m.p. equivalence relation of finite cost
on (X,mu). Let E be any Borel subequivalence relation of R whose classes
are finite almost surely, and prescribe a Borel tree F in each E-class.
Choose a Borel transversal A for E and put q=mu(A)>0. Graphings in this
section can be countable; no uniform degree or group-label bound is
part of the assertion.

### Theorem 5.1: prescribed finite-forest normal form

With the normalized measure mu_A on A,

    C(R) = inf_{J generates R|A} c_mu(F union J)
         = 1-q + q C_mu_A(R|A).                            (7)

In particular, for every eta>0 there is a generating graphing containing
the entire prescribed F whose cost is less than C(R)+eta. The prescribed
trees need not come from subgroup orbits or be chosen optimally.

**Proof.** Orient F toward its representative in A. Every point outside
A has exactly one outgoing edge and every representative has none.
The oriented edge relation splits into countably many partial p.m.p.
isomorphisms, so c_mu(F)=mu(X minus A)=1-q. Equivalently, mass transport
gives q=integral 1/|[x]_E| dmu(x), which also proves q>0.

For any generating graphing J of R|A, F union J generates R: join each
endpoint to its E-representative along F, and join those representatives
using J. No F-edge has both endpoints in A. After omitting loops in J,
the edge sets are disjoint and their costs add:

    c_mu(F union J)=1-q+q c_mu_A(J).

Taking the infimum and using Gaboriau's complete-section induction
formula, Proposition 2.33 of the cited lectures, proves (7). For the
eta assertion choose J within eta/q of its infimum. This uses the
standard induction theorem, not a new deletion theorem. QED.

### Corollary 5.2: simultaneous normal form through a free factor

Let pi:Y->X be as in Section 1 and suppose both action costs are finite.
Lift E and F orbitwise to E_Y and F_Y. Orbitwise bijectivity implies that
each lifted block is finite of exactly the same size as its base block,
and B=pi^{-1}(A) meets it exactly once. Also nu(B)=mu(A)=q.

Theorem 5.1 applies on both spaces. Thus the cost infima of both actions
can be computed while requiring the common forest F and its lift F_Y,
respectively. This supplies a common prescribed part of their graphings
without assuming either action has a generating treeing.

Let

    D = C_mu(R_X)-C_nu(R_Y),
    D_A = C_mu_A(R_X|A)-C_nu_B(R_Y|B).

Subtracting the two induction identities gives the exact scaling

    D = q D_A.                                             (8)

The two restricted relations are still linked by an orbitwise
bijective p.m.p. factor, with their normalized measures. They are not
automatically free actions of one common subgroup of Gamma; treating
them as such would introduce an extra, unproved hypothesis.

Equation (8) controls what a block argument must prove. A sequence with
q_n->0 only yields D=0 if it also yields D_(A_n)=o(1/q_n).
A positive original gap would instead give D_(A_n)=D/q_n exactly.
The existence of arbitrarily large finite blocks is therefore
insufficient on its own. The common forest is free to impose at the
cost infimum, but the unresolved comparison survives in the relation
between its representatives.

The finite-cost assumptions prevent subtraction of infinities. In
particular this argument does not address an extension of finite cost
over a base of infinite cost, a possibility that a universal proof must
also exclude. No finite-generation or ergodicity assumption is used in
(7)--(8).

### Consequence for the next construction

It is legitimate to begin a relative exchange construction with a
chosen finite-block forest included on both spaces at arbitrarily
small cost excess. The remaining work is to compare their connector
graphings on the representatives, including any repair edges. Section
3 completes that work because its quotient graph is a tree with one
available bridge per quotient edge. For general R, equation (7) does
not construct an optimal quotient connector graphing, and (8) prevents
us from mistaking a small transversal for a small comparison gap.

## 6. A quantitative condition that does give connected rounding

Return to a simple generating graphing H of degree at most d, and a
base-measurable equivariant positive contraction 0<=K<=P_Z(H). Partition
each orbit measurably into finite blocks, each with at most M vertices,
such that H restricted to each block is connected. Let P_out be the
coordinate projection onto edges joining different blocks and set

    b(K,E) = Tr(P_out K).

This is an observable weighted boundary measure, with the diagonal of
K as edge weight. It is not a count of components or an uncharged
repair term.

### Theorem 6.1: block-boundary rounding estimate

There is a measurable generating subgraphing H' of H such that

    c(H') <= c(H)-Tr(K)+(1+2d M^2) b(K,E).                  (9)

In the relative setting of Section 1 this becomes

    C(X) <= c(H') <= c(Phi)+(1+2d M^2) b(K,E).             (10)

Unlike determinantal deletion, the construction preserves connectivity
pointwise: choose a spanning tree inside each block and retain every
edge between blocks. Every removed edge has a retained finite path
inside its own block. The work is to bound how much this saves.

**Proof of the estimate.** Let P_in=I-P_out and let P_0 project onto
the orthogonal direct sum of the finite cycle spaces of the induced
block graphs. For v in Z(H), its bounded boundary operator satisfies
partial v=0. Put u=(P_in-P_0)v. On each finite block u is orthogonal
to the kernel of the internal boundary operator, hence is a gradient.
Also

    partial u = -partial P_out v.                         (11)

The unweighted Laplacian of a connected graph with n<=M vertices has
every positive eigenvalue at least 1/M^2. Here is a sufficient elementary
bound. For a mean-zero function f, write its squared norm as
(1/n) times the sum of |f(x)-f(y)|^2 over unordered pairs. Choose a
simple path of length at most n-1 for each pair and use Cauchy--Schwarz
along it. Bounding the number of pairs by n(n-1)/2 gives

    ||f||^2 <= ((n-1)^2/2) ||partial_in^* f||^2
            <= M^2 ||partial_in^* f||^2.

Consequently on the internal gradient space
||u||^2<=M^2 ||partial_in u||^2. Singleton blocks have zero gradient
space and satisfy this assertion as well. Since deg(H)<=d,
||partial w||^2<=2d ||w||^2 for every edge chain w, by Cauchy--Schwarz
at each vertex and counting each edge at its two endpoints. Sum the
block inequalities and use (11) to get

    ||u||^2 <= 2d M^2 ||P_out v||^2.

The internal and external edge spaces are orthogonal, so

    ||(I-P_0)v||^2 <= (1+2d M^2)||P_out v||^2.             (12)

The range of K^(1/2) is contained in Z(H). Apply (12) to K^(1/2)w
and take the finite normalized operator trace. Positivity and cyclicity
of that trace yield

    Tr((I-P_0)K) <= (1+2d M^2) Tr(P_out K).

Also Tr(P_0 K)<=Tr(P_0), because 0<=K<=I. Hence

    Tr(P_0) >= Tr(K)-(1+2d M^2)b(K,E).                     (13)

Choose a Borel representative and spanning tree for each block. If a
block has n vertices and e internal edges, the dimension of its cycle
space and the number of edges deleted are both e-n+1. Averaging with
the p.m.p. edge normalization gives deletion measure exactly Tr(P_0).
Thus c(H')=c(H)-Tr(P_0), which proves (9). Equation (3) then gives
(10). QED.

### What this would need to settle the comparison

For near-optimal source graphings Phi_n, let H_n be their finite-label
conditional-support graphings and K_n the relative operators. The
bound proves cost descent if there are connected finite-block
partitions E_n with degree and size bounds d_n,M_n such that

    (1+2 d_n M_n^2) b(K_n,E_n) -> 0.                       (14)

This is the explicit open premise `fpbs-relative-cycle-block-localization`.
The estimate alone does not supply those partitions. In particular,
vanishing unweighted boundary is not asserted, and even b(K_n,E_n)->0
without the factor depending on d_n,M_n would not suffice for (10).

This premise concerns only the relative surplus. It does not require
the entire cycle space of a near-optimal base graphing to vanish, so
the resulting route does not assert cost--Betti equality. It is an
exact geometric reformulation of factor-cost preservation in the
finitely generated setting: if preservation already holds, lift a
near-optimal finite-label base graphing to the source, giving H_n=Phi_n
orbitwise, K_n=0, and use singleton blocks. Conversely (10) proves
preservation from (14). Its value as a research target is the concrete
boundary estimate and a connected rounding algorithm, not an
independent proof of (14).

The normal form in Section 5 permits a common finite-block forest at
the cost infimum. It does not imply the weighted localization (14),
and does not automatically give the finite-label, bounded-degree
graphings used here. Those are separate requirements of this route.

### A fixed source graphing can resist every finite-block partition

In the example of Section 2, K=P_Z(H) for H=T_(2r) x C_M. Every edge
lies in a simple commutation square. Taking the inner product of its
unit edge vector with the normalized four-edge cycle vector gives

    <K delta_e,delta_e> >= 1/4                             (15)

for every edge. Also every finite vertex set U in this product graph
has at least (2r-2)|U| boundary edges: apply the elementary tree boundary
inequality separately in each cyclic layer and count only horizontal
edges. For any measurable partition into finite blocks, mass transport
therefore gives

    Tr(P_out) = (1/2) integral |boundary B_x|/|B_x| dmu(x)
              >= r-1,
    b(K,E) >= (r-1)/4.                                    (16)

This holds regardless of the block sizes or how they are selected.
Thus this fixed relative certificate cannot satisfy (14), even though
the base has the optimal treeing constructed in Section 3. No
partition-only theorem for every fixed source graphing can establish
the open premise. Varying the near-optimal source graphing, as its
statement allows, is essential.

There is also a concrete limitation of the rounding rule behind (9):
it keeps all crossing edges. Section 3 saves additional cost by keeping
only one bridge between each pair of adjacent cyclic blocks. A future
exchange argument may need that additional operation and a way to
control the resulting quotient cycles. Equations (15)--(16) rule out
trying to obtain the missing universal estimate solely by enlarging
blocks around the unchanged certificate of Section 2.

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
* [Gaboriau, Measure Equivalence, Cost, and L2 Betti numbers](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf),
  Proposition 2.33 and its proof: restriction to a complete section
  scales cost minus one by its measure. Section 5 is a deduction from
  that classical formula, rechecked September 10, 2026. It does not
  invoke a multiplicativity theorem for finite-index subrelations.
* The general problem remains open in our work; its current literature
  status was rechecked September 10 against the references in
  `fpbs-fixed-price-universal`, including the July 2026
  [product-neighbourhood preprint](https://arxiv.org/html/2607.20273v1).

The proofs here are written mathematics, not Lean verification. Cairn
compilation checks their dependency registration and explicit open
boundary. No finite numerical experiment certifies a universal claim.
