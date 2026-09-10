# Cost, cycle dimension, and concentration of relator circulations

Research note — September 9, 2026

## Scope and status

This note develops one structural line of argument for Fixed Price. It does not assert a solution of Fixed Price or Benjamini–Schramm. It does not use the preceding conversation's broad bounded-exponent, two-generator, or small-cancellation claims as premises.

The established background is measured graphing cost, the Hilbert-module interpretation of graphings, and Gaboriau's invariance of first L2-Betti numbers under free p.m.p. actions. The deductions proved here are a quantitative cycle-surgery inequality, its consequences for almost-minimizing graphings, and a presentation-level estimate using cancellation-reduced integer circulations. No priority claim or independent formal/referee verification is asserted.

The key distinction is between the length of a replacement path and the size of the circulation remaining after paths are combined around a relation. The latter permits cancellations and is the relevant quantity in the presentation-level estimate.

## 1. Setup and standard inputs

Let R be an aperiodic countable probability-measure-preserving equivalence relation on a standard probability space (X,mu). Initially suppose R has a bounded-degree graphing. Use simple unoriented Borel graphings: no loops or duplicate edges. For a graphing Phi, let

    c(Phi) = (1/2) integral_X deg_Phi(x) dmu(x),
    C(R) = inf_{Phi generates R} c(Phi).

On the unordered edge space E(Phi), define the finite edge measure

    m_Phi(A) = (1/2) integral_X #{y : {x,y} in A} dmu(x).

Thus m_Phi(E(Phi))=c(Phi). Choosing a Borel orientation and partitioning the oriented edges into partial p.m.p. bijections recovers the usual graphing definition without changing cost. Connectedness always means equality of generated relations modulo null sets.

For a finitely generated countably infinite group Gamma acting freely and p.m.p., bounded-degree finite graphings suffice to approximate the action's cost. Indeed, split a near-optimal countable graphing into restrictions of group transformations and truncate to finitely many pieces. Almost every connection associated with any one of a fixed finite generating set is realized by some finite path in this increasing truncation. Their unrecovered domains have measures tending to zero. Add the original generator on each such domain. This gives finite graphings generating the full relation at costs tending to the original infimum. Removing duplicate unoriented edges does not increase cost.

We use the following standard L2 facts [G02, L, B, S]. For a bounded-degree graphing Phi, the Hilbert R-module C_1(Phi) consists on each orbit of square-summable antisymmetric edge chains, with one unit basis vector per unoriented edge. Its R-dimension is c(Phi). The vertex module has R-dimension one. Von Neumann dimension is additive on orthogonal decompositions, monotone on submodules, and continuous for increasing closed spans. The closed image of a bounded module map has dimension at most that of its domain.

Let Z(Phi) be the closed span of the finite simple-cycle chains, taken fiberwise and measurably. Then

    beta_1^(2)(R) = dim_R(ker partial_1) - dim_R Z(Phi).

One construction fills every finite loop of Phi by a 2-cell. Its fibers are simply connected. Exhausting the attached cells by bounded-length loops gives uniformly locally bounded complexes, with fixed 0- and 1-skeleta. The closed union of the 2-boundary images is precisely Z(Phi). The first-degree case of measured L2-homology invariance supplies the displayed identity. For a free p.m.p. Gamma-action,

    beta_1^(2)(R) = beta_1^(2)(Gamma).

These are imported L2 results; they are not inferred from finite numerical tests.

## 2. A reciprocal-cycle-length surgery inequality

For e in E(Phi), let ell_Phi(e) be the least number of edges in a finite simple cycle containing e. Set ell_Phi(e)=infinity if no such cycle exists, and 1/infinity=0.

### Theorem 2.1

For any finite-cost locally finite graphing Phi generating R,

    C(R) <= c(Phi) - integral_{E(Phi)} 1/ell_Phi(e) dm_Phi(e).    (2.1)

Equivalently, with B_L(Phi) the set of edges lying on a cycle of length at most L,

    m_Phi(B_L(Phi)) <= L [c(Phi)-C(R)]                          (2.2)

for every integer L>=3.

### Proof

For each e on a finite cycle, choose one shortest such cycle Q_e measurably. Local finiteness and a fixed countable Borel ordering give this choice. The collection Q_e is fixed before priorities are assigned.

Consider a priority function r on the unordered edge space with a finite range. Delete e precisely when its chosen cycle exists and all the other edges of Q_e have priorities strictly smaller than r(e). Edges not on a finite cycle are retained.

This deletion preserves the whole generated relation. Induct on the finite priority values. A deleted edge can be replaced by the remaining path in Q_e, whose edges have lower priority. Replacing those edges by their already-recovered finite paths gives a retained-edge path connecting the original endpoints. Lowest-priority edges cannot be deleted. No infinite descent is involved. This proof applies to every priority assignment, including assignments with ties.

To estimate the number of deletions on the original space, choose refining finite measurable partitions of the unordered edge space that separate distinct edges. For each e with a chosen cycle, its finitely many distinct cycle edges eventually occupy distinct partition atoms. Since m_Phi is finite, dominated convergence yields a finite partition whose collision-exception set of edges has m_Phi-measure less than eta.

Give its finitely many atoms independent continuous uniform priorities and replace these by their finite ranks. At each nonexceptional e, its chosen cycle has independent distinct priorities, so e is the largest with probability exactly 1/ell_Phi(e). Consequently,

    E_priorities m_Phi(deleted edges)
        >= integral 1/ell_Phi(e) dm_Phi(e) - eta.

Some deterministic finite ranking attains at least that expected deletion mass. The retained graphing generates R and its cost is at most c(Phi) minus that mass. Send eta down to zero in the cost infimum. This proves (2.1); (2.2) follows from 1/ell>=1/L on B_L. QED.

The coefficient has a finite normalization check. On a single L-cycle with uniform vertex measure, c(Phi)=1, C(R)=1-1/L, and integral 1/ell dm=1/L. Thus equality holds. This is a sharpness check, not a proposed counterexample to a conjecture.

The theorem is a quantitative use of the classical cycle-removal mechanism. It does not claim that an infinite-priority minimal spanning forest generates the relation, or that a canonical forest optimizes action cost.

## 3. The homological accounting identity

Assume Phi has bounded degree and infinite connected components. Its boundary operator

    partial_1 : C_1(Phi) -> C_0

is bounded. The kernel of its adjoint consists of square-summable functions constant on each connected component; since components are infinite, this kernel vanishes. Hence partial_1 has dense image, of R-dimension one. Polar decomposition and additivity give

    dim_R ker partial_1 = c(Phi)-1.

Set z(Phi)=dim_R Z(Phi). The standard first-homology computation from Section 1 now gives the exact identity

    c(Phi) = 1 + beta_1^(2)(R) + z(Phi).                       (3.1)

This separates the dimension carried by gradients (one), reduced first homology, and finite-cycle circulations. The identity is not an assertion that every cycle-space dimension can be removed by a measurable connectivity-preserving edge choice.

Define the nonnegative excess over the homological lower bound

    g(R) = C(R)-1-beta_1^(2)(R).

For a bounded-degree graphing with epsilon=c(Phi)-C(R),

    z(Phi) = g(R)+epsilon.                                    (3.2)

For a free action of Gamma, beta_1^(2)(R) depends only on Gamma. Thus all possible action-dependence of cost lies in g(R). Proving g(R)=0 for every free action would prove the stronger cost–Betti equality, and therefore Fixed Price. Fixed Price alone only asks for g(R) to be action-independent.

The optimized quantity g(R) is the classical cycle rate tau(R),
explicitly recorded with C(R)=1+beta_1(R)+tau(R) in
[Pichot--Vassout, Section 4.3](https://arxiv.org/pdf/0903.0911).
The accounting identity above is not a new cost invariant.

## 4. An exact description of loss at large cycle scales

Let Z_L(Phi) be the closed span of simple cycles having length at most L, and z_L(Phi)=dim_R Z_L(Phi). It is supported on the edges B_L(Phi), so Theorem 2.1 gives

    z_L(Phi) <= m_Phi(B_L(Phi)) <= L epsilon.                  (4.1)

Let

    tau_L(Phi)=z(Phi)-z_L(Phi) >= 0.

Combining (3.2) and (4.1),

    tau_L(Phi) >= g(R)-(L-1)epsilon.                           (4.2)

Now take ANY sequence of bounded-degree graphings Phi_n generating R with c(Phi_n)->C(R). Degrees need not have a common bound across n. For every fixed L,

    z_L(Phi_n)->0,
    z(Phi_n)->g(R),
    tau_L(Phi_n)->g(R).                                      (4.3)

For each individual n, all finite cycles eventually appear as L increases, so

    lim_{L->infinity} tau_L(Phi_n)=0.                          (4.4)

Hence

    lim_{L->infinity} lim_{n->infinity} tau_L(Phi_n)=g(R),
    lim_{n->infinity} lim_{L->infinity} tau_L(Phi_n)=0.          (4.5)

The possible strict cost–Betti gap is exactly this failure to interchange limits. It is not hidden in bounded-length cycle patterns of near-minimizers: those have vanishing edge measure by (2.2).

### Corollary 4.1: cycle-dimension compactness suffices

If for one near-minimizing sequence

    lim_{L->infinity} limsup_{n->infinity} tau_L(Phi_n)=0,

then C(R)=1+beta_1^(2)(R).

Conversely, if that equality holds, the displayed condition follows for every near-minimizing sequence from 0<=tau_L(Phi_n)<=z(Phi_n)->0.

This exact criterion is a structural reformulation, not a proof of the missing compactness. Section 5 gives a more concrete sufficient estimate in terms of a fixed presentation.

## 5. Finite presentations: a bound using reduced circulations, not route lengths

Let

    Gamma=<s_1,...,s_d | r_1,...,r_m>

be an infinite finitely presented group, acting freely and p.m.p. Let Phi generate its orbit relation R and have a finite oriented representation

    Phi={T_{g_j}|_{A_j} : 1<=j<=p},

with no edge duplication after choosing orientation. Thus c(Phi)=sum_j mu(A_j). Each chosen g_j is spelled by a finite word w_j in the fixed s-generators. The collection of g_j and the words w_j can change when Phi changes.

Choose a measurable finite Phi-path P_s(x) from x to xs for each original generator s. For inverse letters use the reverse of P_s(xs^{-1}). No uniform length or integrability of these paths is assumed. Let Q(w,x) denote the integer edge chain obtained by concatenating the corresponding paths along word w, adding oriented coefficients and canceling opposite traversals.

There are two types of closed integer circulations:

    xi_l(x)=Q(r_l,x),                         x in X;
    eta_j(x)=e_j(x)-Q(w_j,x),                 x in A_j,

where e_j(x) is the single oriented Phi-edge from x to xg_j. The endpoint boundaries cancel, so every xi_l and eta_j is a finite integer chain of zero boundary.

For a finite chain xi define

    ||xi||_1=sum_e |coefficient of e in xi|.

This is the mass AFTER cancellations. It is generally different from the length of a representing closed walk. In particular a path followed by its reverse contributes zero regardless of its geometric length. No conclusion about small norm is drawn merely from long-path cancellation being possible.

Define

    T_L(Phi;P,w)
      = sum_{l=1}^m mu{||xi_l(x)||_1>L}
        +sum_{j=1}^p mu{x in A_j:||eta_j(x)||_1>L}.             (5.1)

### Theorem 5.1: circulation-tail rank bound

For every L>=3,

    tau_L(Phi) <= T_L(Phi;P,w).                               (5.2)

### Proof: the listed circulations span the finite-cycle space

Consider a finite closed Phi-walk in a single orbit. Replace each oriented Phi-edge e_j by the canonical s-word w_j, reversing words for inverse traversals. Subtracting the routed canonical walk from the original chain is a sum of the eta_j at the corresponding roots, with signs.

The concatenated canonical word represents the identity in Gamma. Freeness is used here: a group element returning one point of the free orbit must be the identity. By the fixed group presentation, the resulting finite canonical Cayley 1-cycle is a finite integer sum of translated defining-relator boundaries. Apply the edge-path map Q. Its image is a finite sum of xi_l at vertices of the orbit. Thus every finite Phi-cycle chain lies in the span of these two families. Conversely all listed vectors are finite cycle chains. Their closed R-module span is exactly Z(Phi).

### Proof: short vectors lie in Z_L

A finite integer circulation can be decomposed into directed simple cycles with positive integer multiplicities: orient each nonzero coefficient positively, follow a directed edge until a vertex repeats, subtract a simple cycle, and repeat. Zero divergence guarantees continuation, and the total integer mass decreases at every subtraction. Each simple cycle used has length at most the initial total mass.

Therefore ||xi||_1<=L implies xi belongs to Z_L(Phi), even if its support is disconnected or lies far from the root where the walk was based.

### Proof: the long vectors have dimension at most their indexing measure

Take the listed circulation families restricted to their bad domains in (5.1). Their total indexing measure is T_L. The closed R-module span of these long vectors has dimension at most T_L.

For clarity, no boundedness of the full untruncated path-to-chain map is assumed. First restrict every bad domain further to roots where the original representing closed walk has length at most M. Such a walk remains in the Phi-ball of radius M around its root and has coefficients bounded by M. Since Phi has bounded degree and only finitely many families are being indexed, the resulting boundary map from the vertex modules on these domains to C_1(Phi) is bounded: column sizes and the number of possible source roots affecting a target edge are bounded in terms of M, the degree, and the number of families. The dimension of its closed image is at most the dimension of its domain, hence at most T_L. Increase M to infinity. All the walks are finite at their individual roots, so the images exhaust the closed span of the long vectors, and dimension continuity preserves the same bound.

The entire cycle space is generated by its short vectors, already in Z_L, plus the long vectors. Additivity/monotonicity of dimension therefore yields z(Phi)-z_L(Phi)<=T_L. QED.

The argument controls dimension without a global route-length or congestion bound. Truncation is used only to justify bounded operators before taking increasing closed spans.

## 6. A positive cost-descent theorem and a sufficient compactness condition

Put beta=beta_1^(2)(Gamma), c=c(Phi), and [t]_+=max(t,0). Equations (3.1) and (5.2) give

    z_L(Phi) >= [c-1-beta-T_L(Phi;P,w)]_+.

The cycle-surgery proof in Section 2 constructs a generating subgraphing after removing at least z_L/L in the cost infimum, because the support edge measure of Z_L is at least z_L. Consequently,

    C(R) <= c - [c-1-beta-T_L(Phi;P,w)]_+/L.                  (6.1)

For every positive tolerance there is a genuinely generating subgraphing attaining the right side up to that tolerance. Thus this is a descent statement for any supplied finite graphing and routes, not just a numerical inequality about an unknown minimizer.

If epsilon=c-C(R), the same inequalities imply

    0 <= g(R) <= (L-1)epsilon + T_L(Phi;P,w).                  (6.2)

### Corollary 6.1

Suppose Phi_n is a near-minimizing sequence and its choices of routes and edge words satisfy

    lim_{L->infinity} limsup_{n->infinity} T_L(Phi_n;P_n,w_n)=0. (6.3)

Then C(R)=1+beta_1^(2)(Gamma).

Proof. Fix L in (6.2) and let n tend to infinity; then let L tend to infinity. QED.

A concrete sufficient condition is a uniform bound K<infinity on the total mean REDUCED circulation mass

    E_n=sum_l integral ||xi_{l,n}(x)||_1 dmu(x)
          +sum_j integral_{A_{j,n}} ||eta_{j,n}(x)||_1 dmu(x)
        <= K.                                               (6.4)

Markov's inequality gives T_L<=K/L. Equation (6.2) becomes

    g(R) <= (L-1)epsilon_n + K/L.

Again let n, then L, tend to infinity. Uniform bounded expectation is stronger than (6.3); no assertion that it is necessary is made.

The hypothesis concerns circulations after cancellations, not individual generator paths. Divergence of replacement-path lengths therefore does not by itself refute (6.3) or (6.4). Conversely, long paths are not presumed to cancel: the norms in these formulas must actually be controlled by a construction.

Finite presentability supplies a finite list of relators, but does NOT automatically bound their routed circulation norms or the comparison loops eta_j. It also does not justify moving the supremum over a sequence past L->infinity. Those are precisely the missing estimates.

## 7. What this does and does not reduce

For any free action of a fixed finitely generated Gamma,

    C(alpha)=1+beta_1^(2)(Gamma)+g(alpha),   g(alpha)>=0.

Proving g(alpha)=0 for every action would prove the stronger cost–Betti equality and therefore Fixed Price. Proving only that g(alpha) is the same for all free actions would suffice for Fixed Price. Neither claim is established here.

The universally valid positive deductions are:

* explicit finite-priority surgery removes at least the reciprocal shortest-cycle-length integral;
* almost-minimizing graphings have at most L epsilon edge measure on cycles of length at most L;
* any remaining cost–Betti excess is exactly the finite-cycle dimension that persists at unbounded lengths;
* for finitely presented groups, the reduced circulations of defining relators and edge-comparison loops supply a concrete rank-tail bound and cost descent.

The work does not create another specially presented group. It also does not assert that a free minimal spanning forest computes cost, or that a cost-one limit graphing generates an arbitrary nonamenable relation.

This note addresses Fixed Price. Equality of cost with 1+beta would not alone settle Benjamini–Schramm for groups with beta=0. A separate percolation argument is still required in that regime.

## 8. A coherent routing example with bounded reduced mass

September 10, 2026. This calculation tests the hypothesis of Section 6
positively on a known fixed-price-one group. It does not prove that hypothesis
for arbitrary groups, nor claim novelty for the group's cost.

Fix r>=2 and Gamma=F_r x Z with presentation

    <a_1,...,a_r,t | a_i t a_i^(-1) t^(-1), 1<=i<=r>.

Work on one free Bernoulli action with independent uniform [0,1] marks for
each positive a_i-edge at each vertex. Equivalently, use r coordinates per
vertex of a [0,1]^r Bernoulli shift. Retain all t-edges and retain each
a_i-edge when its mark is at most epsilon, where 0<epsilon<1. Write Phi_epsilon
for this graphing. It has cost 1+r epsilon.

For every horizontal edge column and every starting height z, let H_i(z)
be the first retained edge height at least z. Almost surely these heights
are finite simultaneously at all vertices. Route the a_i-request at height z
up to H_i(z), across that retained edge, and back down to height z. Route t
directly. Thus Phi_epsilon generates the full orbit relation. The same
Bernoulli space supports every epsilon in any sequence tending to zero.
The aperiodic cost lower bound and c(Phi_epsilon)=1+r epsilon give C(R)=1;
this is the familiar sparse-column construction, not a new fixed-price result.

### Exact cancellation around the relators

The routed commutator a_i t a_i^(-1) t^(-1) compares the horizontal route
at height z with the one at z+1. If the edge at z is absent, then
H_i(z)=H_i(z+1). Adding the two routes with their inverse orientations
and the two t-steps cancels every edge, giving the zero integer circulation.

If the edge at z is present, set D=H_i(z+1)-z. Then D has the geometric
distribution on {1,2,...} with success probability epsilon, independently
of the event that the edge at z is present. After cancellation, the
commutator is the rectangle between heights z and z+D in the two adjacent
vertical columns. The rectangle has exactly 2D+2 edges, each with coefficient
of absolute value one. No other edges remain.

For the edge-comparison circulations eta_j of Section 5, choose the original
single-letter edge words. A retained horizontal edge routes across itself,
and a vertical edge also routes directly; hence every eta_j is zero.
Writing xi_i for the i-th relator circulation, we obtain

    E ||xi_i||_1 = epsilon (2 E D+2) = 2+2 epsilon,
    sum_i E ||xi_i||_1 + sum_j integral ||eta_j||_1
        = r(2+2 epsilon) <= 4r.                              (8.1)

This verifies the uniform reduced-mass hypothesis (6.4), even though the
expected length of an a_i-request is

    E length(P_(a_i)) = 1 + 2(1-epsilon)/epsilon -> infinity. (8.2)

There is also an exact tail formula. For any integer L>=3, put
m=floor((L-2)/2). Then

    T_L(Phi_epsilon;P,w) = r epsilon (1-epsilon)^m.           (8.3)

For L>=4, m>=1 and the maximum of epsilon(1-epsilon)^m occurs at
epsilon=1/(m+1), by differentiation. Therefore

    sup_(0<epsilon<1) T_L
      = r/(m+1) (m/(m+1))^m
      <= r/floor(L/2) -> 0.                                 (8.4)

Every identity above follows from a geometric waiting time and the explicit
edge cancellation. No finite simulation substitutes for a statement about
all orbits. The construction uses the commuting infinite-order direction t:
successive routes choose the same connector until a retained edge is passed.
No such direction or analogous common routing rule is available here for
an arbitrary group. In particular, the calculation must not be extended to
torsion groups by assuming a vertical line exists.

## 9. The actual conditional route to universal Fixed Price

It is sufficient to prove the cycle-dimension compactness condition only for
Bernoulli actions of finitely generated groups; applying it separately to
every free action would be stronger than needed at this step. More precisely,
suppose that for every infinite finitely generated Gamma its free Bernoulli
action b has near-minimizing bounded-degree generating graphings Phi_n with

    lim_(L->infinity) limsup_(n->infinity) tau_L(Phi_n)=0.     (9.1)

By Corollary 4.1, C(b)=1+beta_1^(2)(Gamma). The published cost--Betti lower
bound then gives C(alpha)>=C(b) for every free action alpha. Abert--Weiss
supplies the opposite inequality, so all free actions of Gamma have equal
cost. Passing from all finitely generated groups to arbitrary countable
groups remains a separate, unproved prerequisite in the current Cairn route.

Condition (9.1) is NOT established. By Section 4 it is equivalent to the
Bernoulli cost--Betti equality, so it is a stronger target than Fixed Price
alone, not a weaker reformulation that has already been solved. Section 8
shows that the concrete sufficient reduced-circulation estimate can coexist
with divergent route lengths in one family; it does not prove (9.1)
universally. For finite presentations, (6.3) implies (9.1). For arbitrary
finitely generated groups the cycle-space formulation makes sense directly,
but the finite relator list in Section 5 is unavailable.

This route is now explicit in `fpbs-bernoulli-lower-bound-from-cycle-tails`.
Its open construction premise is `fpbs-bernoulli-cycle-tail-compactness`.
It uses no assertion that the free minimal spanning forest is connected
or computes cost. Current external status was checked September 10, 2026:
Gaboriau's author-hosted [FAQ](https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/FAQ.pdf)
lists cost--Betti equality as a question, and the introduction of
[Slutsky's July 2026 preprint](https://arxiv.org/html/2607.20273v1)
explicitly describes universal Fixed Price as open. No novelty is claimed
for these reductions or the known class result.

## References and mathematical provenance

[G02] Damien Gaboriau, Invariants l2 de relations d'equivalence et de groupes, Publications Mathematiques de l'IHES 95 (2002), 93–150. Measured L2-homology and invariance. https://www.numdam.org/item/PMIHES_2002__95__93_0/

[L] Damien Gaboriau, Around the orbit equivalence theory, measure equivalence, cost and l2 Betti numbers, author-hosted lecture notes, October 3, 2025. Cost, the cost–Betti inequality, and Hilbert-module background. https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf

[B] Anton Bernshteyn, An l2-based proof of Gaboriau's theorem (2018). Lemma 4.2 identifies graphing cost with edge-module dimension; Sections 1–3 give trace and dimension conventions. https://abernshteyn3.math.gatech.edu/resources/l2.pdf

[S] Roman Sauer, L2-Betti Numbers of Discrete Measured Groupoids, arXiv:math/0312411. Theorem 1.2 (group/action Betti equality), and Section 2 (dimension properties). https://arxiv.org/html/math/0312411v1

[AW] Miklos Abert and Benjamin Weiss, Bernoulli actions are weakly contained in any free action, arXiv:1103.1063v2. Background on the one-sided comparison between action costs; not used to assert the reverse comparison. https://arxiv.org/html/1103.1063v2

Prior conversation file: fixed-price-finite-priority.md, Sections 2–3. The finite-priority induction is reproved on the full unoriented edge space here; no broad group-class conclusion from that file is assumed.

## Verification boundaries

The inequalities above have written proofs. The L2 invariance and dimension facts are imported from the indicated sources. No mass of finite experiments, dependency checker, or status label is offered as verification of those infinite arguments. The universal conjectures and the existence of near-minimizing sequences satisfying (6.3) remain unproved in this work.
