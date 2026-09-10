# Continuation: a quantitative routing obstruction, not a universal solution

## Status

Neither the universal Fixed Price problem nor the universal Benjamini–Schramm
nonuniqueness conjecture is resolved here. In particular, this document does
not replace either open goal in the supplied Cairn material by an assumption
or by a computational check. No priority or formal-proof claim is made for
the lemma below.

The continuation strengthens the earlier qualitative compactness obstruction.
It also records where a separate operator approach stops. All graph distances
below are unweighted shortest-path distances.

## 1. Setting and quantitative statement

Let G = Cay(Gamma,S) be a simple, locally finite, undirected Cayley graph,
with finite symmetric generating set S, degree d = |S|, and root o. Define
its unnormalized edge Cheeger constant by

    h = inf {|boundary_G A| / |A| : A is nonempty and finite}.

The boundary consists of unoriented edges with exactly one endpoint in A.
Assume h > 0. Write B_R for the vertex ball of radius R about o in G.

Let H be a Gamma-invariant random connected spanning subgraph of G, and put

    delta = (1/2) E deg_H(o) - 1.

This delta is a particular graphing's edge-intensity excess, not the excess
of the action cost, which is an infimum. The minimal-expected-degree theorem
for infinite unimodular random graphs gives delta >= 0 [AL, Theorem 6.1].

**Proposition (quantitative routing obstruction).** For every integer R >= 1,

    (1/d) sum_{s in S} P(d_H(o,s) > R)
        >= h/d - delta |B_R|.                                      (1)

The right side may be negative; the useful range is delta |B_R| < h/d.
The result does not assume H is a factor of IID. Additional randomization
used in the proof does not change the law of H or the distances in H.

## 2. Proof

### 2.1 Obtain a sparse deletion with finite components

Conditional on H, sample its wired uniform spanning forest F. The construction
is equivariant in law, so the joint law of (H,F) is Gamma-invariant. The rooted
law of H is unimodular, and every component of F is infinite. The standard
wired-forest mean-degree theorem gives

    E deg_F(o) = 2.                                                 (2)

The component of o in F, with its inherited root distribution, is also a
unimodular random rooted graph. The degree-two characterization therefore
implies that its tree has at most two ends. By Gamma-invariance and
countability, this holds for every F-component almost surely. These imported
results are [AL, Proposition 7.1 and Theorem 6.2], with the numbering in the
linked author-hosted version.

Fix 0 < eta < 1. Delete each F-edge independently with probability eta and
call the retained forest Q_eta. Its components are finite almost surely:
from any given vertex in a locally finite tree with at most two ends, there
are at most two infinite simple rays. Each fixed ray has probability zero
of surviving independent positive-density edge deletion. An infinite locally
finite connected cluster would contain such a ray. Countability completes
the argument simultaneously for all vertices.

Put D_eta = E(H) \ E(Q_eta). Using (2), its edge intensity is

    (1/2) E deg_D_eta(o)
        = (1 + delta) - (1 - eta)
        = delta + eta.                                             (3)

Thus we have a jointly invariant finite-component spanning subgraph of H,
obtained by deleting edge intensity delta + eta. This is the specific step
that the proof needs from spanning-forest theory.

### 2.2 Finite components must expose ambient boundary

Let C_eta(v) be v's Q_eta-component and define

    b_eta(v) = #{w : {v,w} in E(G), C_eta(v) != C_eta(w)}.

Every component C is finite, so

    sum_{v in C} b_eta(v) = |boundary_G C| >= h |C|.

Mass transport gives

    E b_eta(o)
      = E[ |boundary_G C_eta(o)| / |C_eta(o)| ]
      >= h.                                                        (4)

For clarity, the transport proving the equality has v send
b_eta(v)/|C_eta(v)| to each vertex of C_eta(v). Its outgoing mass is b_eta(v)
and its incoming mass is the component average of b_eta.

### 2.3 A short route crossing a component boundary sees a deleted edge

For s in S, if C_eta(o) differs from C_eta(s) but d_H(o,s) <= R, any H-path
of length at most R from o to s must use an edge of D_eta. All the vertices
of that path are in the *ambient* ball B_R, so that edge has both endpoints
in B_R. Consequently, pointwise,

    b_eta(o)/d
      <= (1/d) sum_s 1{d_H(o,s) > R}
         + 1{D_eta intersects E(G[B_R])}.                           (5)

The use of the ambient ball, and counting only edges with both endpoints
inside it, avoids an additional boundary or factor-of-two term.

By Markov's inequality, incidence counting, and invariance,

    P(D_eta intersects E(G[B_R]))
      <= E |D_eta intersect E(G[B_R])|
      <= (1/2) sum_{v in B_R} E deg_D_eta(v)
      = |B_R| (delta + eta).                                       (6)

Take expectations in (5), apply (4) and (6), and then let eta decrease to
zero. This gives exactly (1). QED.

## 3. Consequences

### 3.1 Quantified failure of uniform tightness

For any sequence H_n of invariant random connected spanning subgraphs with
delta_n decreasing to zero, for every fixed integer R >= 1,

    liminf_n (1/d) sum_s P(d_H_n(o,s) > R) >= h/d.                    (7)

This is stronger than merely saying some route lengths are not uniformly
tight. At least the positive fraction h/d survives in the averaged tail at
every fixed length scale, in this limiting sense. It does not assert that
every generator separately has this lower bound.

### 3.2 Explicit logarithmic lower bound on the average mean distance

Nonamenability implies d >= 3. The elementary degree bound is

    |B_R| <= 1 + d((d-1)^R - 1)/(d-2)
           <= d(d-1)^R/(d-2).

Whenever delta > 0 is small enough that

    R_delta = floor(log_{d-1}( h(d-2)/(2 d^2 delta) )) >= 1,

we have delta |B_R_delta| <= h/(2d). Equation (1) implies

    (1/d) sum_s E d_H(o,s) >= [h/(2d)] R_delta.                      (8)

The bound allows infinite expectations. In particular, the averaged mean
replacement distance grows at least logarithmically in 1/delta. This is not
a universal reciprocal lower bound; the earlier F_r x Z construction has a
stronger reciprocal divergence, and nothing here promotes that special rate
to all groups.

### 3.3 Why this is not a Benjamini–Schramm proof

The earlier forest-band-bridge graphings, under a hypothetical equality
p_c = p_u, have delta tending to zero. Equation (1) says their short routes
must fail on a positive fraction of generator pairs. That is consistent
with connectedness of each individual graphing: connectedness ensures
finite distances for each fixed graphing, not uniform distances across the
sequence.

To obtain a contradiction from this construction one would still need a
percolation-specific upper bound contradicting (7). No such upper bound is
proved here. Imposing it as a hypothesis would not prove it for the
percolation graphings under investigation.

## 4. The separate operator route and its unresolved estimate

Let

    T_p(x,y) = P_p(x is connected to y)

be the Bernoulli-percolation connectivity kernel. Hutchcroft's critical
L2-boundedness condition is a sufficient route to a nonuniqueness interval:
boundedness at p_c yields a nontrivial interval above p_c on which the kernel
is bounded on ell^2, whereas uniqueness of an infinite cluster precludes
such boundedness [H].

The latter obstruction has a short proof. Under uniqueness at p > p_c,
FKG and transitivity imply

    T_p(x,y) >= theta(p)^2 > 0

for all x,y: when both vertices lie in infinite clusters, they lie in the
same one. Thus for any finite vertex set A,

    <1_A, T_p 1_A> / ||1_A||_2^2 >= theta(p)^2 |A|,

which is unbounded as |A| tends to infinity.

The missing estimate is not supplied merely by nonamenability. If A_G is
the adjacency operator, a union bound over simple paths and then all walks
gives, entrywise,

    T_p <= sum_{n >= 0} p^n A_G^n,

and therefore ||T_p|| <= 1/(1-p||A_G||) when p||A_G|| < 1. This sufficient
condition need not reach p_c. On the d-regular tree,

    p_c = 1/(d-1),       ||A_G|| = 2 sqrt(d-1).

At degree 4, their product is 2/sqrt(3) > 1, so this bound fails to reach
criticality even on that tree. This is a failure of the walk bound, not a
counterexample to critical L2 boundedness or percolation nonuniqueness.

One can verify the adjacency norm formula directly by a weighted Schur test
with weights (d-1)^(-distance(o,v)/2), giving the upper bound 2 sqrt(d-1),
and by truncating that radial function to growing balls, whose Rayleigh
quotients tend to the same value. The percolation threshold follows from
the Binomial(d-1,p) offspring branching process.

No general replacement for this inadequate walk estimate is established in
this continuation. Treating ||T_p_c|| < infinity as proved would simply
insert the central missing theorem into the argument.

## 5. Fixed Price remains a distinct target

Abert–Weiss gives the Bernoulli action maximal cost [AW]. The continuation
provides neither a free action with strictly smaller cost nor the reverse
cost inequality for every free action. Different graphings H and their
numbers (1/2)E deg_H(o) are not different action costs.

Lyons's implication [L] still identifies the cost-one case as the gap in the
cost-based approach to Benjamini–Schramm: if any Cayley graph has p_c=p_u,
the group has fixed price one. This implication does not imply that fixed
price one forces p_c=p_u, nor that a counterexample to Benjamini–Schramm
would be a counterexample to Fixed Price.

## 6. Archive and validation scope

A term search of all Markdown/TeX entries below two megabytes in the original
ZIP returned 19 matching files for fixed-price, Benjamini–Schramm,
percolation, cost-one, or graphing terms. This is a text audit, not a complete
mathematical certification of the archive. The routed-phase-repair note
explicitly retains quantitative routing and phase-compatibility hypotheses.

The accompanying finite replay tests only the deterministic witness and
incidence-counting inequalities (5)-(6) on finite graphs. It does not verify
the infinite spanning-forest results, measurability, or either conjecture.
Cairn checks dependencies and artifact references; it is not a mathematical
proof checker. Both universal goal nodes remain OPEN.

## References

[AL] David Aldous and Russell Lyons, Processes on Unimodular Random Networks.
Author-hosted version of 28 December 2005, Theorems 6.1-6.2 and Proposition
7.1. Published in Electronic Journal of Probability 12 (2007), 1454-1508.
https://www.stat.berkeley.edu/~aldous/Papers/me-russ.pdf

[H] Tom Hutchcroft, The L2 boundedness condition in nonamenable percolation.
arXiv:1904.05804, revised 23 September 2020.
https://arxiv.org/abs/1904.05804

[AW] Miklos Abert and Benjamin Weiss, Bernoulli actions are weakly contained
in any free action, arXiv:1103.1063v2, Corollary 2.
https://arxiv.org/html/1103.1063v2

[L] Russell Lyons, Fixed Price of Groups and Percolation,
arXiv:1109.5418v1.
https://arxiv.org/html/1109.5418v1
