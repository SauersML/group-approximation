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

## 5. What has and has not been advanced

The iteration now has a valid positive-contraction invariant and an
exact cost identity. Its definition no longer loses a hypothesis
after the first exchange. The original source graphing need not be
reconstructed at each step, and the retained graphing stays connected
by its explicit finite paths.

There is still no rule selecting exchanges that makes the surviving
trace tend to zero for arbitrary factors. Independent cycle priorities
do not do so, and acyclicity of a limiting edge set does not force
that conclusion. No universal residual estimate, countable-group
passage, or exclusion of finite-cost extensions over infinite-cost
bases has been proved.

These are written deductions over the identified operator and
spanning-forest inputs. Cairn compilation checks registration and
dependencies; it is not independent mathematical or Lean verification.
