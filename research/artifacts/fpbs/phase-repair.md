# Error-tolerant torsion repair and the exact finite-phase obstruction

Research continuation — September 9, 2026

## Status

This note proves an error-tolerant relative-cost inequality for arbitrary measurable subrelations, not only subgroup orbit relations. It also gives an elementary finite-index zero-relative-cost proof and computes exactly what happens when one selects one or several phases of a finite skew-product action.

These are written mathematical deductions, not independently refereed or formally verified results. No novelty or priority claim is made. Neither universal Fixed Price nor universal Benjamini–Schramm is solved. In particular, the large odd-exponent Burnside Bernoulli cost remains undetermined. The finite checks accompanying this note do not establish the infinite assertions.

The important change in the research program is that positive-density phase disagreements need not require positive repair cost. Finite-index phase connections admit arbitrarily cheap shared repairs. However, selecting a single phase restores the cost suppressed by finite-sheet normalization. Those two facts have to be accounted for separately.

## 1. Conventions

Let a countable group Gamma act essentially freely and probability-preservingly on a standard probability space (X,mu). Work on a common invariant conull free set. Use right actions x -> xg.

Write R for its orbit equivalence relation. A subrelation S <= R is a countable measurable p.m.p. equivalence relation, understood modulo null sets. It need not be the orbit relation of a subgroup. Let

    Delta_S(b) = mu{x : (x,xb) is not in S}.

For S <= T <= R, relative cost is

    relC(T;S) = inf{Cost(Psi) : S join R_Psi = T}.

All added maps below are restrictions of group transformations. Countably partitioning a map according to the translating group element preserves its summed domain measure. The standard cost lower bound for an aperiodic relation is one. The complete-section formula is

    C(R)-1 = mu(Y) (C(R|Y, normalized measure)-1).             (1.1)

The small-complete-section and induction facts are imported from Gaboriau [G, Exercise 1.17 and Proposition 2.33]. They are not statements about multiplicativity of cost under arbitrary finite-index subgroup restriction.

## 2. The finite error-tolerant repair theorem

Fix a in Gamma. Suppose b_1,...,b_k are chosen so that

    c_i = a b_i,           d_i = ord(c_i),           2 <= d_i <= N,
    P_i = {c_i,c_i^2,...,c_i^(d_i-1)}

are pairwise disjoint subsets of Gamma. The group need not have bounded exponent: only these particular cycles have orders bounded by N.

For each root x define the admissibility event

    A_i(x)  <=>  (x c_i^j a, x c_i^(j+1)) belongs to S
                 for every j=0,...,d_i-1.                    (2.1)

Thus every b_i-step around the c_i-cycle is already available in S. No independence among the A_i is assumed.

### Theorem 2.1 (exact finite budget)

For every 0<q<1 and eta>0 there is a graphing Psi such that

    S join R_Psi = S join R_{T_a},

and

    Cost(Psi) <= q + integral product_{i:A_i(x)}(1-q^(d_i-1)) dmu(x)
                  + eta.                                    (2.2)

An empty product is one.

Put

    ebar_k = (1/k) sum_i min(1, d_i Delta_S(b_i)).

Then for each 0<theta<1 the construction also gives

    Cost(Psi) <= q + ebar_k/(1-theta)
                  + exp(-theta k q^(N-1)) + eta.             (2.3)

The formulas count graphing cost, not the total length of the paths inside S.

### Proof

Choose a finite measurable partition P of X separating the points xg for g in the finite set F=union_i P_i, except at a set of roots of measure below eta. To justify this, use refining finite partitions separating points in a standard Borel model. For g!=h, freeness gives xg!=xh almost surely. The probability of a collision in an atom tends to zero, and there are finitely many pairs.

Temporarily color each partition atom selected with probability q, independently, and let U be the union of selected atoms. This auxiliary finite randomization chooses a deterministic measurable set after averaging; it does not replace the given action.

Call x a failure when no admissible cycle has all its required a-edge starting points in U:

    D(U) = {x : for every i with A_i(x), some xc_i^j is outside U,
                      1 <= j < d_i}.

For every root outside the exceptional set, the tested points occupy distinct atoms, so

    P_colors(x in D(U)) = product_{i:A_i(x)} (1-q^(d_i-1)).

Also E_colors mu(U)=q. After integration and averaging there is a deterministic U with

    mu(U)+mu(D(U)) <= q + integral product_{i:A_i(x)}(1-q^(d_i-1)) dmu(x)
                       + eta.

Add T_a restricted to U and T_a restricted to D(U), or just to their union. For a failure root the direct a-edge is present. For a successful root select an admissible i with all xc_i^j selected. The path

    xa --b_i--> xc_i --a--> xc_i a --b_i--> xc_i^2 --a--> ...
       --b_i--> xc_i^d_i = x

uses only S-steps and selected a-edges. All a-connections are recovered. Every added edge is an a-edge, so the joined relation is exactly S join R_{T_a}. This proves (2.2).

For (2.3), put M_k(x)=sum_i 1_{A_i(x)}. The product in (2.2) is at most exp(-q^(N-1) M_k(x)). Each failure of A_i is the failure of at least one b_i-connection. Each test root xc_i^j a has distribution mu, hence

    mu(A_i^c) <= min(1,d_i Delta_S(b_i)).                      (2.4)

Thus E(k-M_k)<=k ebar_k, and Markov's inequality gives

    mu(M_k < theta k) <= ebar_k/(1-theta).

Split the integral over that set and its complement to obtain (2.3). QED.

### Important qualifications

* S is fixed before the finite atom-coloring randomization. Its connection failures may be arbitrarily correlated.
* The finite separating partition only has to separate the required group-coordinate points. S itself is not approximated or silently replaced.
* The proof controls the SUM of selected and directly repaired edge costs, not separate concentration bounds for one specially chosen set U.
* Existing S-steps can be expanded into finite paths in a graphing of S on a common conull set. Their lengths can be enormous and do not enter this relative-cost ledger.
* The theorem is not a transport theorem between two different actions. It repairs a graphing already present in the target action.

## 3. Infinite families and average-error bounds

Suppose now that a fixed sequence (b_i)_{i>=1} satisfies the same disjointness and order bound. Define

    B = {x : only finitely many of the A_i(x) occur}.

### Theorem 3.1

    relC(S join R_{T_a};S) <= mu(B)
        <= liminf_{k->infinity} (1/k) sum_{i=1}^k mu(A_i^c)
        <= liminf_{k->infinity} (1/k) sum_{i=1}^k
                                    min(1,d_i Delta_S(b_i)). (3.1)

In particular,

    relC(S join R_{T_a};S)
       <= N liminf_k (1/k) sum_{i=1}^k Delta_S(b_i).          (3.2)

### Proof

Fix q>0 and let k tend to infinity in (2.2), using dominated convergence. Outside B the product tends to zero, because infinitely many factors are at most 1-q^(N-1)<1. On B it is at most one. For every eta>0 this gives a relative-cost upper bound q+mu(B)+eta. Send q and eta to zero.

On B, the fraction of inadmissible indices tends to one. Everywhere else its liminf is nonnegative. Fatou's lemma therefore gives

    mu(B) <= liminf_k (1/k) sum_i mu(A_i^c).

Now use (2.4). QED.

### A finite generating set

Let Gamma=<a_1,...,a_r>. Suppose that for every a_j there is such a disjoint family (b_{j,i}) with the same order upper bound N. Then

    C(R) <= C(S) + N sum_{j=1}^r eps_j,                     (3.3)

where

    eps_j = liminf_k (1/k) sum_{i=1}^k Delta_S(b_{j,i}).

Choose almost optimal additions for each generator and join them to S. No nesting of the different families is needed. Overlap between families for different generators is allowed, since they are selected and repaired separately.

This is a robust extension of the earlier subgroup detour lemma. The earlier case has S=R_H, b_i in H, and all errors zero. Equation (3.3) remains valid for a subrelation with no subgroup interpretation and only small AVERAGE connector errors.

For the Bernoulli action of a finitely generated group, producing subrelations S_m with

    C(S_m) -> 1,       sum_j eps_{j,m} -> 0

would prove Bernoulli cost one by (3.3), and hence fixed price one by Abert-Weiss [AW]. Those subrelations and estimates are NOT constructed for arbitrary groups or for large odd free Burnside groups in this note.

## 4. Finite-index connection repair has infimum zero

### Proposition 4.1

Let R be an aperiodic countable p.m.p. relation. If S<=R and each R-class is a union of at most q S-classes, then

    relC(R;S)=0.                                            (4.1)

For every R-complete section A, there is a graphing Psi generating R relative to S with

    Cost(Psi) <= (q-1) mu(A).                               (4.2)

The index may vary below q. The proposition also extends to finite almost-everywhere index without a uniform bound, by splitting into R-invariant index strata and allocating a summable error budget.

### Proof

Choose an arbitrarily small R-complete section A, using [G, Exercise 1.17]. Enumerate the group transformations generating R (in our application R is an action relation; the standard general representation of countable p.m.p. relations gives the same argument).

At every x in A, choose the first point in the enumeration that is not S-related to x, then the first point in a still unrepresented S-class, and continue until all S-classes in R[x] are represented. There are at most q-1 extra representatives. Membership in S and countable enumeration make all choices measurable.

A chosen representative map is piecewise a group transformation. Partition its domain according to that group element. Each piece is an injective partial p.m.p. map. The costs of its pieces sum to at most mu(A). Add all the resulting maps for the at most q-1 representative slots.

Every R-class has a root in A. The star at that root joins all its S-classes. Thus S plus the added graphing generates R, at cost at most (q-1)mu(A). Sending mu(A) to zero proves (4.1). QED.

This is an elementary application of the standard small-marker method. No claim of novelty is attached to the finite-index statement. It does not prove an index-multiplication formula for C(S)-1 and C(R)-1.

For a finite generating set, the added graphing can be truncated to finitely many pieces, with the remaining generator-connection errors made arbitrarily small and directly repaired. This follows by continuity from below of finite-path connection events. No uniform bound on the necessary truncation is asserted.

## 5. Exact phase selection and its normalization cost

Let pi:Gamma -> Z/qZ be a surjection, q>=2, with infinite kernel K. Let alpha be a free p.m.p. action on (X,mu) such that alpha|K is ergodic. Define the free skew-product action

    beta((x,j),g) = (xg, j+pi(g))

on (X x Z/qZ, nu=mu x uniform). It is ergodic: K acts ergodically on each sheet, and Gamma permutes all the sheets transitively.

Write

    kappa = C(alpha|K),

and assume kappa<infinity for the displayed finite-value calculations.

The constant sheet Y_0=X x {0} is complete for R_beta and has measure 1/q. Its restricted relation is alpha|K. Therefore the induction formula (1.1) gives

    C(beta) = 1+(kappa-1)/q.                                (5.1)

### Theorem 5.1 (every one-phase choice has the same section cost)

For ANY measurable c:X -> Z/qZ, let

    Y_c={(x,c(x)):x in X},
    S_c={(x,xg): c(xg)=c(x)+pi(g)}.

Then, on normalized measure,

    C(S_c)=kappa,                  relC(R_alpha;S_c)=0.       (5.2)

### Proof

The graph Y_c has measure 1/q. Since R_beta is ergodic, it is a complete section modulo null sets. Projection Y_c -> X is measure-preserving for normalized restricted measure, and identifies R_beta|Y_c with S_c. The latter is a subequivalence relation: the displayed cocycle equality composes and inverts.

Induction gives

    C(S_c)-1 = q(C(beta)-1)=kappa-1.

The base alpha-action is free. Over a fixed alpha-orbit, the q lifted beta-orbits are disjoint, since a return to the same base point must be the identity group element. Completeness of Y_c means it meets each of them. Thus the alpha-orbit splits into exactly q S_c-classes almost surely. Proposition 4.1 gives zero relative cost. QED.

The theorem applies to an optimally selected phase, a highly nonlocal measurable phase, or a phase depending on all the Bernoulli coordinates. The compression factor is unchanged.

### Several phases

Let M(x) be a measurable subset of Z/qZ, and put

    Y_M={(x,j):j in M(x)},       m=integral |M(x)| dmu(x)>0.

Ergodicity makes Y_M a complete section. Its measure is m/q, so

    C(R_beta|Y_M, normalized) = 1+(kappa-1)/m.               (5.3)

For exactly k selected phases at every x this is 1+(kappa-1)/k.

This is an exact statement about a relation on a multi-sheet space. When m>1 it is NOT a graphing on the original probability space with one point per base vertex. Simply projecting every selected edge does not preserve the normalized cost ledger. No unrestricted theorem about arbitrary folding procedures is asserted here.

### Why this revises the proposed strategy

The cheap-looking value in (5.1) is a genuine cost of beta. However, returning to one measurable phase multiplies the excess cost back by q. Repairing the resulting phase relation is free in the infimum, but its starting cost is kappa, not 1+(kappa-1)/q.

Thus the finite-phase selection route cannot create a cost reduction by choosing a clever section and then cheaply reconnecting it. This does not exclude a fundamentally different transformation of graphings, or transport from the infinite-quotient action used in [DS].

## 6. Specialization to the previous odd-exponent Burnside candidate

For sufficiently large odd n (take n>=1003 for the algebraic inputs below), let Gamma=B(2,n). The inputs from [DS, Lemma 2.4 and Theorem 2.5] are:

* centralizers of nontrivial elements are cyclic of order n;
* every noncyclic subgroup contains a copy of B(infinity,n), and hence B(2,n).

Here is a short rederivation of the upper-cost comparison needed for this section, so the other broad claims in the earlier notes need not be taken as premises.

For infinite H<=Gamma and a outside H, the coset aH meets infinitely many distinct nontrivial centralizers. Distinct centralizers intersect trivially: a nontrivial element in their intersection puts both original elements in one abelian centralizer, which implies equality. Choose c_i=ab_i in distinct centralizers. Their nonidentity power sets P_i are disjoint. All have order at most n.

Apply Theorem 3.1 with S=R_H. Every connector defect is zero. Enumerating the remaining group elements with summable costs gives C(alpha)<=C(alpha|H) for every free action. The same proof applies inside any infinite subgroup of Gamma, because its centralizers remain abelian and uniformly finite.

For K=ker(pi), where pi(a)=1, pi(b)=0 in Z/nZ, K is infinite and finite index, and contains a copy J of Gamma by the embedding input. Taking upper costs yields

    Cmax(Gamma) <= Cmax(K) <= Cmax(J)=Cmax(Gamma).

Denote this common value c_n. It obeys 1<=c_n<=2-2/n: each order-n generator has a cyclic orbit treeing of cost 1-1/n.

Let alpha be a free Bernoulli Gamma-action. Its restriction to K is Bernoulli, obtained by regrouping the finitely many regular K-orbits of the coordinate index set. Both Gamma and K are finitely generated, so [AW, Corollary 2] gives

    C(alpha)=C(alpha|K)=c_n.

Consequently the exact conclusions of Section 5 become

    C(beta)=1+(c_n-1)/n,
    C(S_c)=c_n                     for every measurable phase c,
    relC(R_alpha;S_c)=0,
    C(R_beta|Y_M)=1+(c_n-1)/m.                            (6.1)

No value of c_n has been determined here. If c_n>1 the two actions alpha and beta have different costs; if c_n=1 the family has fixed price one. The paper [DS] proves infimal group cost one, not c_n=1, and explicitly separates those statements.

## 7. Positive phase-disagreement density can coexist with zero repair cost

This auxiliary calculation makes the difference between direct-edge repair and shared-path repair quantitative.

Let Gamma be nonamenable and finitely generated by a finite symmetric set T, and let

    P = (1/|T|) sum_{s in T} lambda(s),     rho=||P||<1

on l2(Gamma). Let alpha be a Bernoulli action and c:X -> Z/qZ a BALANCED phase labeling, mu(c=j)=1/q for every j. Then

    (1/|T|) sum_{s in T} mu{c(xs)!=c(x)+pi(s)}
          >= (1-rho)(1-1/q).                              (7.1)

### Proof

For each nontrivial character chi_l of Z/qZ, z_l(x)=chi_l(c(x)) is mean zero and has L2 norm one. Twist the Bernoulli Koopman operators by the scalar character chi_l(-pi(s)). On the mean-zero subspace, this twisted representation is weakly contained in the regular representation and its averaging operator has norm at most rho.

For clarity about this input: the mean-zero Bernoulli Koopman representation embeds in a direct sum of regular representations [H]. One can see this by decomposing into elementary tensors indexed by finite nonempty coordinate supports. Such a support has finite translation stabilizer; its stabilizer representation embeds in multiples of the regular representation of that finite group. Inducing embeds the corresponding orbit of tensors in a multiple of the group regular representation. Twisting by a group character preserves the regular averaging norm by a diagonal unitary change of basis on l2(Gamma).

Using the character identity for equality mod q, average over s and integrate:

    (1/|T|) sum_s mu{c(xs)=c(x)+pi(s)}
      = (1/q) sum_{l=0}^{q-1} (1/|T|) sum_s
             integral conjugate(z_l(x)) chi_l(-pi(s)) z_l(xs) dmu
      <= 1/q + ((q-1)/q)rho.

This proves (7.1). QED.

In contrast, S_c has zero relative cost by Section 5. Thus the sum of direct generator-disagreement measures is only an upper bound on a particular direct repair scheme, not a lower bound on optimized graphing repair cost. Long shared rerouting is permitted by cost theory. No contradiction with the earlier routing obstructions is asserted.

For q=2 and the standard four-generator symmetric set of F_2, rho=sqrt(3)/2. The average disagreement lower bound is (1-sqrt(3)/2)/2, while the optimized relative repair cost is zero. This illustrative example concerns repair cost, not unequal action costs.

## 8. Exact remaining problem

A productive application of Theorem 3.1 would construct low-cost subrelations S_m INSIDE the target Bernoulli action, along with disjoint torsion-detour families for the generators, such that

    C(S_m) -> 1,
    sum_j liminf_k (1/k) sum_i Delta_{S_m}(b_{j,i}) -> 0.

The resulting fixed-price-one conclusion would follow from (3.3). This note does not construct that sequence in the large odd-exponent Burnside group, much less universally. The phase kernels S_c do not supply it unless c_n was already one, because their cost is exactly c_n.

Neither the pivotal-sensitivity estimate for Benjamini–Schramm nor a new comparison of arbitrary free actions has been proved here. The finite-index repair theorem and the orbitwise detour theorem do not justify changing the universal goal statuses.

## 9. Verification scope

The standard-library replay checks arbitrary subrelations in finite groups, not just subgroup cosets. It verifies repaired connectivity for all vertex colorings in the chosen models, exact rational selector expectations, and the union-bound estimate in (2.4). It separately enumerates finite-index star completions and checks single- and multi-phase compression identities in finite cyclic models.

Finite models can have noncomplete phase sections. The script detects and excludes those from the induction calculation; it does not silently assume the infinite ergodicity hypothesis in a finite model.

The replay does not verify any infinite convergence argument, the small-marker theorem, the cost induction theorem, Bernoulli maximality, the Burnside algebra, or the spectral statement. The written arguments and named references specify those roles.

Cairn checks dependency structure and artifact existence, not mathematical validity. Earlier notes are retained as provenance; only the detour and common-upper-cost inputs used here are rederived. Both universal goals remain OPEN.

## References

[G] Damien Gaboriau, Around the orbit equivalence theory, measure equivalence, cost and l2-Betti numbers, 2025 lecture notes. Exercise 1.17 (small complete sections), Proposition 2.33 (induction), Proposition 2.39 (relative cost). The normalization and small-section statements were visually checked against PDF pages 6 and 15 (zero-index pages 5 and 14).
https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf

[AW] Miklos Abert and Benjamin Weiss, Bernoulli actions are weakly contained in any free action, arXiv:1103.1063v2, especially Corollary 2 for finitely generated groups.
https://arxiv.org/html/1103.1063v2

[DS] Miguel Donoso-Echenique and Eduardo Silva, Free Burnside groups of large odd exponent have cost 1, arXiv:2608.20472v1, August 20, 2026. Theorem 1.2 concerns infimal cost; the paragraph following it explicitly leaves fixed price open. Lemma 2.4 and Theorem 2.5 provide the centralizer and subgroup embedding inputs used in Section 6.
https://arxiv.org/html/2608.20472v1

[H] Ben Hayes, Harmonic Models and Bernoullicity, arXiv:1904.03528, introductory discussion of regular embeddings of mean-zero Koopman representations of Bernoulli factors. The finite-support-tensor argument is also given in Section 7 above.
https://arxiv.org/html/1904.03528

Prior conversation notes: fixed-price-two-generator-complete-proof.md and fixed-price-percolation-torsion-actions.md. They are background and provenance, not substitutes for the new proofs above.
