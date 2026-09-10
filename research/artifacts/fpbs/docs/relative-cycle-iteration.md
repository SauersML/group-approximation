# Iterating connected cycle exchanges without amplifying the certificate

September 10, 2026. This note proves a contractive transport rule and its
exact cost accounting. It also tests the repaired iteration against the
known independent-priority obstruction. The universal Fixed Price
conjecture remains unresolved. The arguments use classical polar
decomposition and the finite-trace module framework already imported in
`relative-cycle-exchange.md`; no mathematical priority is claimed.

## 1. The path image need not remain a positive contraction

Let H be a bounded-degree generating graphing, J a generating spanning
subgraph, and R a bounded equivariant path retraction as in Section 7 of
`relative-cycle-exchange.md`. That section proves

    c(J)<=c(H)-Tr(K)+Tr(R K R^*)

for every positive contraction K. Positivity survives under R K R^*,
but the upper bound by the identity need not survive.

A finite calculation isolates the issue. Take three internally disjoint
paths A,B,C between two vertices, of lengths 1,2,2. This is a simple
four-vertex graph with two triangles sharing their direct edge A.
Retain A and B and one edge of C. Replace the deleted C-edge by its
path through A and the retained part of C. Orient all three paths
from the first common endpoint to the second.

The cycle vectors c_1=A-B and c_2=C-B have Gram matrix

    G = [[3,2],[2,4]],

and R c_1=R c_2=c_1. The unique nonzero eigenvalue of
R P_Z(H) R^* on the retained cycle space is

    ||c_1||^2 (1,1) G^(-1) (1,1)^T = 9/8.

Thus it is not a positive contraction. This is a finite linear-algebra
example about the proposed update rule, not a counterexample to Fixed
Price. It shows why the hypothesis needed at the next iteration cannot
simply be carried over unchanged.

## 2. Contractive transport by polar decomposition

View R as an operator in the ambient H-edge module, fixing the
coordinate subspace C_1(J). Put W=ker R and let P_W be its orthogonal
projection. The deleted-edge isomorphism w->w-Rw gives

    Tr(P_W)=c(H)-c(J).                                    (1)

For a general positive contraction K, take V=W^perp. The restriction
A=R|V maps V boundedly and bijectively onto C_1(J). Its inverse sends
u in C_1(J) to P_V u: indeed R P_V u=u, and this inverse is a
contraction. Consequently A^*A>=I_V. Write its polar decomposition

    A=U |A|,

where U is an equivariant unitary from V onto C_1(J). Define

    K' = U (P_V K P_V)|V U^*.

Then K' is a positive contraction supported on J, and

    Tr(K')=Tr(K)-Tr(P_W K)<=Tr(K),                         (2)
    Tr(K')<=Tr(R K R^*).                                  (3)

For (3), R vanishes on W, so the right side is
Tr(|A|^2 (P_V K P_V)|V). Subtracting Tr(K') leaves the trace
of the product of the two positive operators |A|^2-I_V and
(P_V K P_V)|V, which is nonnegative. The operators need not commute.

### Retaining cycle support

For iteration we need more than support on retained edges. Suppose
0<=K<=P_Z(H). Use instead

    V=Z(H) intersect W^perp,
    A=R|V:V->Z(J).

The path hypotheses ensure W is contained in Z(H): it is the closed
span of the finite circulations e-Re. They also ensure R maps Z(H)
into Z(J), first on finite cycles and then by boundedness. For any
u in Z(J), P_V u=u-P_W u belongs to V and R P_V u=u. Hence this
A is again boundedly invertible, with inverse of norm at most one.
Its polar unitary therefore maps V onto Z(J).

The same definition of K' now gives

    0<=K'<=P_Z(J),                                        (4)

while (2)--(3) are unchanged: K has no component outside Z(H), and
P_Z(H)=P_W+P_V. All projections, restrictions, and polar decompositions
are measurable equivariant operators in the finite-trace framework.

The cycle version is the one to iterate. Applying the polar
decomposition on the full edge module without this restriction need
not preserve cycle support. The construction does not claim that
K' is itself the conditional projection difference of a new source
graphing; only the stated operator properties are used below.

### Exact cost identity

Put

    eta=Tr(P_W(I-K))>=0.

Combining (1)--(2) gives

    c(J)=c(H)-Tr(K)+Tr(K')-eta.                           (5)

In particular c(J)<=c(H)-Tr(K)+Tr(K'). Together with (3),
this recovers the earlier path-retraction bound. The correction
removes the extra trace caused by the nonisometric part |A| of R;
it does not guarantee a strict decrease of Tr(K).

## 3. An iteration that remains within its hypotheses

Let H_0 contain a generating source graphing Phi after lifting through
a free factor. Let K_0 be its relative cycle operator, so

    Tr(K_0)=c(H_0)-c(Phi).

Choose a decreasing sequence of measurable generating graphings H_n,
with a bounded equivariant path retraction R_n from H_n onto H_(n+1)
at every finite stage. No uniform bound in n is assumed. Use the
cycle version of Section 2 to transport K_n to K_(n+1), and define
eta_n using its corresponding kernel projection. Then

    0<=K_n<=P_Z(H_n),
    Tr(K_(n+1))<=Tr(K_n),
    c(H_n)-Tr(K_n)=c(Phi)-sum_{i<n} eta_i.                 (6)

This is induction from (4)--(5), with no unsupported assertion that
the transported operator is another genuine relative projection.
In particular every stage satisfies

    C(X)<=c(H_n)<=c(Phi)+Tr(K_n).                         (7)

If such choices make Tr(K_n)->0, (7) gives C(X)<=c(Phi).
Choosing source graphings with costs tending to C(Y) would then
give the desired factor-cost comparison. Connectivity of the
intersection of all H_n is not needed for this implication: every
finite stage is already a valid competitor for C(X).

The missing assertion is decay of the trace. Monotone nonnegative
sequences can have positive limits. The following test shows that
this is a concrete issue even when the edge sets eventually contain
no finite cycles.

## 4. The known priority obstruction survives contractive transport

Take Gamma=F_2 x Z and its Cayley graph G=T_4 x Z. Let X carry
independent continuous edge priorities. The established claim
`fpbs-priority-deletion-density-above-action-cost` supplies a number
delta_G>0 such that every finite-priority graphing H_(r,m) has cost
at least 1+delta_G. Every such graphing generates and contains the
free minimal spanning forest associated with the priorities.

These inputs are the previously audited deductions from
[Lyons--Peres--Schramm, Minimal spanning forests](https://arxiv.org/abs/math/0412263),
the nonuniqueness theorem for T_4 x Z, and the known fixed-price-one
value for F_2 x Z. They are not consequences of the present transport
calculation.

There is an actual relative starting certificate over this base.
Adjoin independent horizontal-edge Bernoulli marks of probability p,
retain every vertical edge and the marked horizontal edges upstairs,
and call that source graphing Phi. Every adjacent pair of vertical
columns has a retained crossing almost surely, so Phi generates.
Its cost is 1+2p. Its conditional-support base graphing is all of G.
The relative operator K_0 therefore has trace 2-2p.

Take p small enough that 2p<delta_G. Choose increasing cycle-length
cutoffs and dyadically refining priority levels. The resulting H_n
are nested and generating. The finite-priority induction supplies
uniform finite replacement lengths at each stage. Bounded degree
then supplies finite congestion bounds, so each transition admits
the bounded path retraction required in Section 3.

After contractive transport, (6) gives

    Tr(K_n)=c(H_n)-c(Phi)+sum_{i<n} eta_i
           >=delta_G-2p>0                                (8)

at every stage. Thus repairing the operator update does not repair
this graph-selection algorithm's known failure of optimality.

Indeed the intersection of these H_n is the free minimal spanning
forest. An edge excluded from that forest is the unique maximum on
some finite cycle, whose ordering is eventually detected by the
dyadic priorities and length cutoff. Conversely every forest edge
is retained at every stage. The intersection is acyclic, but (8)
still prevents the transported trace from vanishing.

One can also see why a naive continuity argument for cycle spaces
fails here. The projections P_Z(H_n) decrease. The dimension identity,
with beta_1(F_2 x Z)=0, gives Tr(P_Z(H_n))=c(H_n)-1>=delta_G.
Their intersection projection therefore has positive trace by
normality of the finite trace, whereas the finite-cycle space of
the limiting forest is zero. Closed cycle spaces need not commute
with this decreasing edge-set intersection.

Here beta_1=0 identifies Z(H_n) with the full square-summable
boundary kernel at each stage. The surviving intersection therefore
consists of square-summable divergence-free chains supported on the
forest. Such chains may have infinite support. Their existence is
compatible with the absence of finite cycles.

This rules out a claimed universal decay theorem based only on
bounded finite-stage replacements, contractivity of the transported
operator, and eventual removal of every finite cycle. It does not
rule out a different adaptive choice of graphings, exchanges that
add edges, or a proof of Fixed Price by another method.

## 5. Adding edges with their full cost charged

The decreasing edge-set hypothesis can be removed from the exchange
framework, provided additions are accounted for before each deletion.

Let H already generate an aperiodic p.m.p. relation R. Add a measurable
set A of previously absent edges of R, and write H^+=H union A.
Assume H^+ has bounded degree and set a=m_(H^+)(A), so
c(H^+)=c(H)+a. Let P and P^+ project onto Z(H) and Z(H^+), using
the enlarged edge module and extending P by zero.

Since these cycle spaces are nested, Q=P^+-P is an orthogonal
projection. Both graphings generate the same relation, so the
cost--Betti dimension identity gives

    Tr(Q)=z(H^+)-z(H)=c(H^+)-c(H)=a.                       (9)

For 0<=K<=P, define

    K^+=K+Q.

The summands act on orthogonal subspaces. Hence

    0<=K^+<=P^+,
    Tr(K^+)=Tr(K)+a,
    c(H^+)-Tr(K^+)=c(H)-Tr(K).                            (10)

No bounded-path assumption is needed for this addition step. Every
added edge already has a finite path in H because H generates R,
but such paths need not have uniform length. Equation (9) uses the
dimension identity rather than an unjustified bounded routing map.

Now choose a bounded path retraction from H^+ onto a generating
retained graphing J and apply Section 2 to K^+. If W is its kernel,
the resulting contraction K' satisfies

    c(J)-Tr(K')=c(H)-Tr(K)-eta,
    eta=Tr(P_W(I-K^+))>=0.                                (11)

Thus additions preserve the cost-minus-trace quantity exactly, and
deletions can only decrease it. The added edges are charged in both
the graphing cost and the certificate; they are not free repairs.

### Nonmonotone iteration

Starting from a relative certificate with
c(H_0)-Tr(K_0)=c(Phi), alternate these additions and bounded
connected deletions. Then every resulting graphing H_n generates
the original relation, every K_n remains a positive contraction on
Z(H_n), and

    c(H_n)-Tr(K_n)=c(Phi)-sum_{i<n} eta_i,
    C(X)<=c(H_n)<=c(Phi)+Tr(K_n).                          (12)

Trace itself need not decrease across an entire add-then-delete
step. If the added edge cost at step n is a_n and the deletion
captures t_n=Tr(P_W K_n^+), then

    Tr(K_(n+1))=Tr(K_n)+a_n-t_n.                          (13)

Consequently a claim of decay must control t_n against both the
current trace and the new cost a_n. When sum a_n is finite, (13)
implies that the nonnegative traces converge: their total positive
variation is bounded by sum a_n. It does not imply that their limit
is zero. No general construction providing the needed capture is
proved here.

This extension permits changes of the retained edge set in both
directions. It does not prove that any chosen exchange rule escapes
the obstruction in Section 4.

## 6. Why a forest limit cannot be treated as a generating intermediate stage

The common-relation hypothesis in (9) is essential. In the example
G=T_4 x Z, let F be the free minimal spanning forest and write
c(F)=1+delta_G with delta_G>0. Its finite-cycle space is zero, but
its components define a subrelation that need not be the original
orbit relation. In fact it cannot be the full relation here: a
generating treeing would attain the action cost, which is one.

[Lyons--Peres--Schramm, Theorem 3.22](https://arxiv.org/pdf/math/0412263)
proves that F union omega_epsilon is connected almost surely, where
omega_epsilon is independent Bernoulli edge percolation of any
positive parameter epsilon. Realize the two independent label
fields together and put H_epsilon=F union omega_epsilon. If
a_epsilon is the expected edge measure actually added outside F,
independence gives

    a_epsilon=epsilon(c(G)-c(F))->0,
    c(H_epsilon)=1+delta_G+a_epsilon.

This new graphing generates the full F_2 x Z orbit relation, whose
first L2 Betti number is zero. Its finite-cycle dimension is therefore

    z(H_epsilon)=delta_G+a_epsilon.                       (14)

It would be wrong to apply (9) with H=F and conclude that the new
cycle dimension is only a_epsilon. The generated relation changed.
The additional delta_G in (14) is exactly the drop of the first
Betti number from the forest subrelation to the full relation.
All F-components are infinite: the least-priority edge across any
finite vertex cut is retained by the free minimal spanning forest.
The forest treeing has beta_1=c(F)-1=delta_G, whereas the full
relation has beta_1=0.

Sprinkling therefore gives a connected graph at arbitrarily small
added cost, but its total cost remains at least 1+delta_G. An argument
must still remove that excess. Regenerating finite cycles does not
by itself supply a cost-reducing choice among them. This calculation
uses the stated spanning-forest theorem and dimension identities;
it is not a new connectivity theorem or a universal descent bound.

## 7. A finite exchange cannot lower the edge count of a forest

There is also an elementary restriction on what a finite exchange
can accomplish. Let F be any forest, remove a finite set D of its
edges, add a finite set A of new edges, and set J=(F minus D) union A.
Suppose every original F-component is contained in a J-component.
Then

    |D|<=|A|.                                            (15)

To prove this, consider the k original F-components meeting endpoints
of D or A. Deleting D splits them into k+|D| pieces, since a finite
number of cuts in a tree increases its component count by that
number. In the graph on these pieces, adding A must leave at most k
components: each original F-component has to be reconnected, though
different original components may also be merged. Each added edge
reduces component count by at most one, proving (15).

This is a finite-support statement. It does not extend automatically
to infinitely many simultaneous measurable exchanges, and it gives
no lower bound on the cost of a superrelation of the forest relation.
In particular, the full relation in Section 6 has cost one despite
the forest subrelation's larger cost. A proposed algorithm based on
finite local exchanges must identify how its globally coordinated
operations go beyond the finite counting argument, rather than
assume that a single finite improving move always exists.

## 8. A spectral restriction on every permitted exchange sequence

The update rules retain an obstruction that is invisible in the trace
ledger alone. All spectral projections below are taken on the cycle
module Z(H_n), not on the full edge module. In particular, zero
eigenvalues on noncycle edges are not counted. Set

    N_n(t)=Tr(1_[0,t](K_n|Z(H_n))),       0<=t<1.

For every sequence of the additions and polar compressions above,

    N_(n+1)(t)<=N_n(t)<=N_0(t).                           (16)

Here and below one step may comprise both an addition and a deletion.
For addition, the enlarged cycle module is Z(H) direct-sum ran Q
and K^+=K direct-sum I_Q. Thus N(t) is unchanged for t<1.

For compression, write B=(P_V K P_V)|V before the polar unitary.
Let E=1_[0,t](B) and F=1_(t,1](K), viewed as projections in the
old cycle module. Their ranges have zero intersection: a nonzero
vector v in both would satisfy

    <Kv,v>=<Bv,v><=t||v||^2

and also <Kv,v>>t||v||^2, by the spectral support of F. The strict
inequality follows by integrating lambda-t>0 against the nonzero
spectral measure of v; no spectral gap above t is needed. The
finite-module dimension formula for intersections now gives

    Tr(E)<=Tr(I-F)=N_old(t).

Unitary transport preserves this trace. This proves (16) without
assuming that K and P_V commute or that their spectra are discrete.

Write b=1+beta_1(R) and g=C(R)-b>=0. These are finite in the present
bounded-degree setting. Every H_n generates the same aperiodic
relation, so the dimension identity gives

    z(H_n)=c(H_n)-b>=g.

Combining this with (16) yields, for 0<t<1,

    Tr(K_n)>=t(z(H_n)-N_n(t))
            >=t(g-N_0(t)).                               (17)

Let kappa=Tr(ker(K_0|Z(H_0))). Normality of the finite trace gives
N_0(t)->kappa as t decreases to zero. Consequently

    Tr(K_n)->0  implies  C(R)<=b+kappa.                   (18)

In particular, if K_0 has zero kernel on its cycle module, the
proposed trace-zero conclusion would force C(R)=1+beta_1(R).
If g>kappa, choose t with N_0(t)<g; (17) is a fixed positive lower
bound on every iterate's trace, regardless of the added edges or
the chosen bounded retractions. This is a conditional obstruction:
no example with g>0 is being asserted.

For an actual initial relative certificate K_0=E[P_H-P_Phi|X],
its kernel has a concrete meaning. For v in Z(H)_x,

    <K_0 v,v>=integral ||(P_H-P_Phi,y)v||^2 dnu_x(y).

Thus its kernel consists of the cycle chains lying in Z(Phi)_y
for conditionally almost every source fiber. These are common
source cycles, rather than the average amount of source cycle
dimension. In particular

    kappa<=Tr(P_H-K_0)=c(Phi)-b.                          (19)

Equation (18) can therefore demand strictly more than
C(X)<=c(Phi). Averaging and then repeatedly compressing the same
certificate does not retain all the geometric information about
which source cycles vary from fiber to fiber.

## 9. Zero-kernel relative certificates occur arbitrarily near action cost

The zero-kernel hypothesis in Section 8 is not merely a formal choice
of an arbitrary positive operator. It can occur for genuine relative
certificates over an elementary extension of any free action that
has a bounded-degree generating graphing H.

Partition the finite simple cycles of H into countably many Borel
families C_j, each consisting of pairwise vertex-disjoint cycles
of one fixed finite length. Here is a direct justification of the
measurability and countability needed. Represent each cycle by a
canonical finite tuple using a Borel injection of X into [0,1].
For fixed length, the graph joining cycles that share a vertex has
finite degree, since H has bounded degree. A countable family of
Borel sets separates points of this standard Borel cycle space.
For each cycle choose the first finite binary membership string
that distinguishes it from all its finitely many neighbors, and
color by the length and string. Adjacent cycles cannot have the
same color. This supplies the claimed countable partition.

For each family C_j, choose one edge per cycle measurably and delete
just those edges from H, obtaining J_j. Because the cycles in the
family are vertex-disjoint, each deleted edge has its remaining
cycle path in J_j. Thus J_j generates and there is a bounded path
retraction R_j. Put Q_j=P_Z(H)-P_Z(J_j). For a vector v in Z(H),
Q_j v=0 means v belongs to Z(J_j). Every vector of Z(J_j) has zero
coordinate on each edge deleted in this family. To see that
intersection_j Z(J_j) is zero on Z(H), choose the deleted edges so
that every edge lying in a finite cycle is deleted in some family:
repeat each length/color family once for each of its cycle edge
positions, selecting that position in the repetition. Every
finite-cycle chain is supported on this set of edges, and so is
its closed span. A vector in all Z(J_j) vanishes on that support.
Hence

    intersection_j ker(Q_j|Z(H))={0}.                    (20)

Pad the list with empty families if necessary. The repetitions need
not be disjoint from one another: they define
different J_j, never simultaneous deletions. Each J_j individually
still has bounded replacement paths and generates.

Let Gamma act on Y=X x {0,1,2,...} by acting on X and fixing
the countable second coordinate. Fix 0<epsilon<1. Give 0 mass
1-epsilon and j>=1 mass epsilon p_j, with p_j>0 and sum p_j=1.
This is a standard probability
space and the action is essentially free. Define Phi to equal H
on component 0 and J_j on component j. It generates on every
component. Since every component is an invariant copy of X,

    C(Y)=C(X),
    C(X)<=c(Phi)<=c(H).

The first equality follows directly by restricting a graphing to
the countably many invariant components for the lower bound and
copying a near-optimal graphing of X to all components for the
upper bound. It uses no Fixed Price assumption. The conditional
support of Phi is H, because the component 0 retains all its edges.
The genuine relative operator is

    K_0=epsilon sum_j p_j Q_j.

This norm-convergent positive sum has zero kernel on Z(H), by (20).
When Z(H) is zero the assertion is understood on the zero module.

For finitely generated groups, the finite-label approximation
already established in the relative-exchange artifact lets H be
chosen with c(H)<C(X)+delta for any delta>0. Thus Phi is within
delta of C(Y), while its relative K_0 has zero kernel. No uniform
positive lower bound on the spectrum is claimed or needed.

A theorem driving the trace to zero for *every* such near-optimal
relative initialization would, by Section 8, prove the stronger
cost--Betti equality for every finitely generated free action.
It would not merely prove equality of action costs. The distinction
between those two open problems is explicitly recorded in
[Gaboriau's FAQ, page 1](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/FAQ.pdf).
This consequence does not rule out a specially chosen initialization,
a different operator update, or a direct control of the full cost
ledger. It concerns decay with one fixed initial certificate; the
lower bound in (17) need not be uniform when the initialization
changes with the requested approximation error. The invariant-copy
examples are not asserted to be the prescribed Bernoulli product
factor in the reverse-comparison problem. They test a proposed
theorem quantified over all free factors and all initializations.

## 10. The stopping criterion must retain the accumulated saving

Let s_n=sum_{i<n} eta_i. The exact ledger (12) says

    c(H_n)-c(Phi)=Tr(K_n)-s_n.                            (21)

Thus a stage with Tr(K_n)-s_n<=delta already proves
C(X)<=c(Phi)+delta. Requiring Tr(K_n)->0 discards s_n and is only
a sufficient condition. The preceding spectral argument shows why
this distinction matters: a positive residual may be harmless if
it is paid for by the accumulated eta terms.

This does not give an exchange-selection theorem. Indeed, after
adding cost a_n and deleting a set of cost d_n=Tr(P_W),

    (Tr(K_(n+1))-s_(n+1))-(Tr(K_n)-s_n)=a_n-d_n.

Controlling the signed quantity is exactly the actual edge-cost
improvement; no improvement follows just by renaming the ledger.
Any further use of the spectral certificate must justify a choice
of geometric exchanges that obtains that improvement. The audit
removes an unnecessarily strong stopping target without supplying
the missing choice.

## 11. What has and has not been advanced

The iteration now has a valid positive-contraction invariant and an
exact cost identity, including fully charged edge additions. Its
definition no longer loses a hypothesis
after the first exchange. The original source graphing need not be
reconstructed at each step, and the retained graphing stays connected
by its explicit finite paths.

There is still no rule selecting exchanges that makes the full signed
cost excess tend to zero for arbitrary factors. Annihilating the
certificate trace is stronger: Sections 8--9 show that a universal
version for all genuine initializations would force cost--Betti
equality, even for near-optimal self-extensions. Independent cycle priorities
do not do so, and acyclicity of a limiting edge set does not force
that conclusion. No universal residual estimate, countable-group
passage, or exclusion of finite-cost extensions over infinite-cost
bases has been proved.

These are written deductions over the identified operator and
spanning-forest inputs. Cairn compilation checks registration and
dependencies; it is not independent mathematical or Lean verification.
