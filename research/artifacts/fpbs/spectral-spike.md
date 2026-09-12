# Finite-cluster spectral control and the necessary pivotal spike

Date: 2026-09-08 (America/Chicago).

## Status

Neither the universal Fixed Price problem nor the universal Benjamini–Schramm conjecture is solved in this continuation. The results below give an exact finite-cluster spectral bound, a uniqueness-phase spectral decomposition, a quantitative necessary condition for a collapsed percolation window, and a counterexample to a purely partition-theoretic continuity argument. No priority claim is made. Standard representation, sharpness, and critical-finiteness theorems are identified explicitly. The finite replay is an algebra check, not a verification of the infinite proofs.

All percolation statements, unless explicitly called a toy partition model, concern ordinary independent Bernoulli bond percolation on a fixed, locally finite Cayley graph of an infinite finitely generated group. The chosen graph is nonamenable. The issue is the every-generating-set quantifier, not the existence of a favorable generating set.

## 1. Notation and published inputs

Let G=Cay(Gamma,S), where S is finite, symmetric, and excludes the identity. Let d=|S|. Use the lazy simple random walk with transition operator

    P = (I + d^(-1) sum_(s in S) lambda(s))/2.

Its operator norm rho on l2(Gamma) satisfies 0<rho<1. Put

    lambda_0 = -log rho > 0,
    r_n = P(X_n=o),
    c = p_c(G),
    theta(p) = P_p(|C(o)|=infinity),
    a_n(p) = P_p(o connected to X_n).

The walk and percolation are independent. The standard spectral-radius formula for the lazy walk is

    lim_n r_n^(1/n) = rho.                                    (1.1)

One proof uses the spectral measure of P at delta_o. It is supported in [0,rho], its top support point is rho, and its n-th moments are r_n. The top support assertion follows from translation invariance: a nonzero spectral projection has a positive diagonal somewhere, hence at every vertex.

The imported percolation facts are:

* No infinite cluster exists at c on a nonamenable Cayley graph [CF].
* There is K>0 and eta>0 such that theta(c+epsilon)>=K epsilon for 0<epsilon<=eta [DT].
* At any fixed parameter the number of infinite clusters is almost surely 0, 1, or infinity; uniqueness is monotone in the parameter in the standard threshold sense [LS, AFH].

For the second input it suffices to use the published inverse-temperature form. Write beta(p)=-log(1-p), beta_c=-log(1-c). Then [DT] gives theta(p)>=(beta(p)-beta_c)/beta(p). Taking eta=(1-c)/2 and B=-log((1-c)/2), one obtains theta(c+epsilon)>=epsilon/B for 0<epsilon<=eta. Thus K=1/B is one permissible choice. No special critical exponent is assumed.

We use the standard fact that the mean-zero Koopman representation of a Bernoulli shift embeds in a direct sum of left regular representations [H]. A proof sufficient for this note is supplied next.

## 2. Bernoulli covariance bound, including its proof

### Lemma 2.1

Let Z(v) be a real square-integrable factor of iid vertex process on Gamma with E Z(o)=0. Then

    0 <= E[Z(o)Z(X_n)] <= rho^n E[Z(o)^2].                    (2.1)

The expectation includes the random walk.

### Proof

Work on a Bernoulli space A^Gamma large enough to carry all the independent coordinates. Let U_g be its Koopman operators and M=(I+d^(-1)sum_s U_s)/2. The left side of (2.1) is <Z(o),M^n Z(o)>.

Choose an orthonormal basis of L2(A) consisting of the constant and mean-zero functions. Tensor products with nonempty finite support form an orthonormal basis of L2_0(A^Gamma). Gamma permutes this basis. The stabilizer of any such tensor is finite: it preserves a nonempty finite subset of Gamma, and the left-translation action on that subset is free. Each orbit representation is therefore l2(Gamma/H) for a finite subgroup H, and embeds in l2(Gamma) by identifying coset functions with normalized right-H-invariant functions. Taking the direct sum gives ||M|| on L2_0 <=rho.

Since S is symmetric, M is self-adjoint. Its lazy definition makes it positive: the spectrum of the nonlazy self-adjoint contraction lies in [-1,1]. Consequently M has spectrum in [0,rho] on L2_0. Its n-th moments are nonnegative and bounded by rho^n times the squared norm. This proves (2.1). QED.

Ordinary edge iid labels can be constructed equivariantly from sufficiently rich vertex iid labels even when S has involutions. Assign independent half-edge uniforms U_(v,s), and give {v,vs} the label (U_(v,s)+U_(vs,s^-1)) modulo one. Different unoriented edges use disjoint coordinates, so these labels are independent uniform random variables. Extra vertex coordinates supply independent priorities and signs. Thus the use of a vertex Bernoulli space loses no bond-percolation generality.

## 3. All finite-cluster contributions are spectrally controlled

Define

    f_n(p) = P_p(o connected to X_n, |C(o)|<infinity).

### Theorem 3.1

For every p in [0,1] and every n>=0,

    (1-theta(p)) r_n <= f_n(p) <= (1-theta(p)) rho^n.          (3.1)

Moreover f_n(p) is the n-th moment of a finite positive measure supported in [0,rho], with total mass 1-theta(p). For every p<1,

    lim_n f_n(p)^(1/n) = rho.                                 (3.2)

### Proof

Give each vertex an independent continuous priority and an independent fair sign, independent also of the percolation. In each finite cluster select the vertex with smallest priority and assign its sign to every vertex of that cluster. Assign value zero to vertices of infinite clusters. Call the resulting real process F_p(v).

This is an equivariant measurable factor of iid. It does not select a root or a sign in any infinite cluster. Conditional on the percolation and priorities, different finite clusters use distinct independent signs. Therefore

    E[F_p(o)F_p(x)] = P_p(o connected to x, |C(o)|<infinity),
    E F_p(o)=0,
    E F_p(o)^2=1-theta(p).

Lemma 2.1 gives the upper bound. The event X_n=o contributes exactly (1-theta(p)) r_n, giving the lower bound. The spectral theorem applied to F_p(o) and M supplies the claimed measure. For p<1 the probability that all d incident edges are closed is (1-p)^d>0, so 1-theta(p)>0. Equation (1.1) and the two bounds imply (3.2). QED.

In particular, since theta(c)=0,

    r_n <= a_n(c) <= rho^n,
    lim_n n^(-1)log a_n(c) = log rho.                          (3.3)

This recovers the critical walk-correlation bound using finite-cluster coloring. It is consistent with the established co-spectral-radius theory [AFH], and is not presented as a new discovery of that theory.

## 4. An exact decomposition of the infinite-cluster obstruction

Let

    D_n(p) = P_p(o and X_n lie in different infinite clusters).

Write J_p(v)=1{|C(v)|=infinity}-theta(p). This is a mean-zero factor of iid, with variance theta(p)(1-theta(p)). Put

    b_n(p) = E[J_p(o)J_p(X_n)].

Lemma 2.1 yields

    0 <= b_n(p) <= theta(p)(1-theta(p)) rho^n.                 (4.1)

Splitting the event that both endpoints belong to infinite clusters according to whether their clusters are equal gives the exact identity

    a_n(p)+D_n(p) = theta(p)^2 + f_n(p)+b_n(p).               (4.2)

Thus, for every p,

    theta(p)^2 <= a_n(p)+D_n(p)
                 <= theta(p)^2+(1-theta(p)^2)rho^n.           (4.3)

In particular, D_n(p)>=theta(p)^2-a_n(p). This is a useful finite-n witness for distinct infinite clusters when the right side is positive.

### Theorem 4.1: uniqueness-phase spectral decomposition

If there is a unique infinite cluster at p, then there is a finite positive measure nu_p supported in [0,rho] such that

    a_n(p)=theta(p)^2 + integral_[0,rho] t^n d nu_p(t),       (4.4)
    nu_p([0,rho])=1-theta(p)^2.

Consequently,

    theta(p)^2 <= a_n(p)
               <= theta(p)^2+(1-theta(p)^2)rho^n.             (4.5)

### Proof

Under uniqueness D_n(p)=0. Both f_n and b_n are spectral moments of the same positive Bernoulli walk operator on its mean-zero space, by their constructions. Add their two spectral measures. Their masses add to

    (1-theta)+theta(1-theta)=1-theta^2.

The support is contained in [0,rho]. Equations (4.4) and (4.5) follow. QED.

These spectral measures concern averaged random-walk sampling. They are not the spectral measure of the unbounded connectivity convolution operator T_p on l2(Gamma). Confusing the two would be an error.

Equation (4.4) isolates a spectral atom of mass theta(p)^2 at 1, while all remaining mass lies at or below rho<1. The atom can have arbitrarily small weight without changing the n-th-root limit from 1. Thus fixed-n convergence does not control the support edge. A hypothetical collapse can create this atom immediately above c without violating any finite-cluster bound above.

## 5. Exact crossover law along uniqueness parameters

This section strengthens the previous integrated-budget observation without assuming a new percolation estimate.

Suppose p_n are parameters with uniqueness, and suppose

    gamma = lim_n [-n^(-1)log theta(p_n)^2]

exists in [0,infinity]. Then

    lim_n n^(-1)log a_n(p_n) = -min(gamma,lambda_0).           (5.1)

Indeed, the lower bound max{theta(p_n)^2,r_n} comes from uniqueness and the return event. The upper bound theta(p_n)^2+rho^n follows from (4.5). The logarithm of a sum of two positive terms differs from the larger logarithm by at most log 2. Equation (1.1) gives (5.1).

For R>=n, let a_(n,R)(p) be the connection probability restricted to the induced ball B_R(o), still averaged over X_n. The earlier finite-volume Russo identity gives

    M_(n,R)(p) = n^(-1)log[a_(n,R)(p)/a_(n,R)(c)].

Passing R to infinity first and using (3.3) and (5.1) gives

    lim_n lim_R M_(n,R)(p_n) = (lambda_0-gamma)_+.             (5.2)

This is conditional only on the p_n belonging to a uniqueness phase. It is not a construction of such parameters approaching c. The crossover occurs when theta(p_n)^2 has the same exponential order as rho^n.

## 6. Collapse forces exponentially high pivotal spikes

The preceding work identified concentration into every fixed right-neighborhood of c. The next statement makes the necessary scale exponential in the walk length.

Let E_(n,R) be connection from o to X_n in B_R(o), and let N_(n,R) count open pivotal edges for that event when it occurs. In finite volume, Russo differentiation is exact:

    d/dp log a_(n,R)(p)
      = E_p[N_(n,R) | E_(n,R)] / p.                           (6.1)

For completeness, condition first on X_n. The derivative of the finite increasing connection event is the sum of pivotal probabilities. Pivotality is independent of the tested edge's state; making it open forces the event. Thus E[N 1_E]=p a'(p), and division by a(p)>0 proves (6.1). The average over X_n does not depend on p, so it commutes with this finite differentiation.

### Theorem 6.1

Assume, for this theorem only, that p_c(G)=p_u(G)=c. Fix

    0<alpha<lambda_0/2.

For every sufficiently large integer n there are a finite radius R_n>=n and a parameter

    c<t_n<c+exp(-alpha n)

such that

    E_(t_n)[N_(n,R_n) | E_(n,R_n)]
       >= [c(lambda_0-2alpha)/2] n exp(alpha n).              (6.2)

### Proof

Let epsilon_n=exp(-alpha n) and q_n=c+epsilon_n. Under the collapse assumption, uniqueness holds at q_n. For large n, the sharpness lower bound in Section 1 gives

    theta(q_n)>=K epsilon_n.

Uniqueness and positive association, or (4.5), then give

    a_n(q_n)>=theta(q_n)^2>=K^2 exp(-2alpha n).

By finite-volume approximation choose R_n>=n large enough that

    a_(n,R_n)(q_n)>=(K^2/2)exp(-2alpha n).

No bound on this radius has been asserted. At criticality, (3.3) implies

    a_(n,R_n)(c)<=exp(-lambda_0 n).

Consequently,

    log[a_(n,R_n)(q_n)/a_(n,R_n)(c)]
       >= (lambda_0-2alpha)n + log(K^2/2).                    (6.3)

The finite-volume logarithmic derivative in (6.1) is continuous on [c,q_n]. The mean-value theorem gives an interior t_n where its value is at least the right side of (6.3) divided by epsilon_n. For all sufficiently large n that quantity is at least

    [(lambda_0-2alpha)/2] n exp(alpha n).

Multiplying by t_n>=c proves (6.2). QED.

### Corollary 6.2: an exponential-rate obstruction

Fix p_0 in (c,1), and define the extended nonnegative number

    L_n(p_0) = sup_(R>=n) sup_(c<=p<=p_0)
                   n^(-1) E_p[N_(n,R)|E_(n,R)].

If collapse holds, then

    liminf_n n^(-1)log(1+L_n(p_0)) >= lambda_0/2.              (6.4)

Indeed, for each alpha<lambda_0/2 the witness in Theorem 6.1 lies in [c,p_0] for all sufficiently large n; constants disappear after taking a logarithm divided by n. Let alpha increase to lambda_0/2.

Therefore, proving for some p_0>c that

    limsup_n n^(-1)log(1+L_n(p_0)) < lambda_0/2                (6.5)

would establish p_c(G)<p_u(G). A uniform subexponential bound on L_n would be sufficient. This permits substantially more growth than the earlier uniform linear pivotal budget: the latter makes L_n bounded.

**Unproved step:** no proof of (6.5), or of its subexponential special case, is supplied for every nonamenable Cayley graph. Equation (6.2) is not a contradiction: finite R_n can be very large, and a finite connection event can have a large number of pivotal edges. The elementary bound N_(n,R)<=|E(B_R)| does not rule it out. Uniformity in R is essential; a bound only for one radius does not suffice.

## 7. A monotone FIID partition model realizing the spectral jump

The following is explicitly not bond percolation on G.

Give each vertex an independent uniform U_v. For t in [0,1], let B_t={v:U_v<=t}. Define a partition Pi_t with B_t as one class and every vertex outside B_t as a singleton. Empty B_0 is ignored. The partitions increase with t, and their law is an equivariant factor of iid. For every t>0, B_t is infinite almost surely and is the unique infinite class. At t=0 every class is a singleton.

For distinct vertices x,y,

    P(x equivalent to y in Pi_t)=t^2,

while this probability is one when x=y. Thus the walk-sampling probabilities are exactly

    a_n^toy(t)=t^2+(1-t^2)r_n.                                (7.1)

Every fixed-n function is a polynomial and hence continuous from the right at zero. Nevertheless,

    lim_n a_n^toy(0)^(1/n)=rho,
    lim_n a_n^toy(t)^(1/n)=1 for every t>0.                    (7.2)

Moreover,

    n^(-1)log[a_n^toy(t)/a_n^toy(0)] -> -log rho

for every fixed t>0, while for fixed n the same expression tends to zero as t decreases to zero. The limiting sensitivity concentration therefore occurs in a monotone FIID partition model with completely explicit finite-n formulas.

It also exhibits exponential peaks of the normalized logarithmic derivative. Since

    d/dt log a_n^toy(t)
      = 2t(1-r_n)/[r_n+(1-r_n)t^2],                           (7.3)

the maximum over 0<=t<=1 (for r_n<1/2) occurs at

    t_n=sqrt[r_n/(1-r_n)],

and equals

    sqrt[(1-r_n)/r_n].                                       (7.4)

By (1.1), the n-th logarithmic rate of this peak is lambda_0/2, even after division by n. This matches the exponential scale of the logarithmic-sensitivity spike used to derive (6.4), but is not a sharpness example for Bernoulli edge-pivotal counts. The toy parameter has threshold zero, and it is not the ordinary bond-retention parameter with critical value c>0. In particular, identifying its logarithmic derivative with the pivotal count in (6.4) would be an error.

Why Pi_t is not a percolation counterexample: for every 0<t<1 the probability that o lies in B_t but none of its d neighbors lies in B_t is

    t(1-t)^d>0.

There is almost surely such an isolated selected vertex by ergodicity. It belongs to the unique infinite partition class but cannot be connected to its other vertices using edges of G whose vertices remain in that class. Thus the classes are not connected clusters in the fixed ambient Cayley graph. This is precisely the geometric information discarded by a bare partition or spectral argument.

## 8. Relation to Fixed Price and the remaining universal gap

The cost-percolation argument in the earlier note proves the known Lyons implication that threshold collapse forces fixed price one, using Bernoulli maximality [L, AW]. It leaves the nonamenable fixed-price-one groups as the remaining class for that approach.

Nothing in the finite-cluster coloring construction produces a generating graphing of an arbitrary free action, or transfers a low-cost graphing of one action to a Bernoulli action. The inequalities between graphing costs and action costs cannot be replaced by equality without proof. Consequently this continuation neither constructs two different-cost free actions nor proves equality of costs for all free actions.

For Benjamini–Schramm, the exact remaining target in this continuation is the upper estimate (6.5) for every nonamenable Cayley graph, or another genuine obstruction to the scenario in Theorem 6.1. We have not proved that target. The new spectral decomposition explains why the finite-cluster estimate alone is not enough: a tiny positive mass at 1 dominates long-time sampling.

A recent literature check included Chu's September 5, 2026 revision [CF], which still distinguishes absence of an infinite cluster at p_c from absence of a unique cluster at p_u. These are different statements: when p_c=p_u, both can hold because there are no infinite clusters at the common threshold. No implication p_c<p_u may be inferred merely by combining those two endpoint facts.

## 9. Verification and research graph

`scripts/replay_spectral_spike.py` checks the finite sign-covariance identities for set partitions, the two-point finite-volume Russo identity on small graphs, the exact toy-model peak identity, and the finite-matrix toy sampling formula. Exact checks use rational arithmetic. These checks do not establish the infinite Bernoulli representation theorem, critical finiteness, transitive sharpness, or either universal conjecture.

The new Cairn claims distinguish derived statements from the OPEN universal pivotal-rate estimate. The route from that estimate to the Benjamini–Schramm goal remains conditional. The Fixed Price goal is unchanged and OPEN. Cairn compilation checks dependency structure, not mathematical validity. Prior nodes and artifacts are retained as provenance and are not all independently re-verified by this continuation.

## References

[H] Ben Hayes, *Harmonic Models and Bernoullicity*, arXiv:1904.03528. Introductory discussion of mean-zero Koopman representations of Bernoulli factors. The needed spectral fact is also proved in Section 2 above.
https://arxiv.org/abs/1904.03528

[AFH] Miklos Abert, Mikolaj Fraczyk, Ben Hayes, *Co-spectral radius for countable equivalence relations*, arXiv:2205.06692v4 (2024), especially Sections 4 and 5.
https://arxiv.org/abs/2205.06692

[CF] Tasmin Chu, *Applications of the cluster graphing*, arXiv:2608.06644v2, September 5, 2026. Theorem 1.1 gives an exposition of the established critical-finiteness theorem; Theorem 1.6 and Section 1.B concern absence of uniqueness at p_u, not universally strict threshold separation.
https://arxiv.org/abs/2608.06644

[DT] Hugo Duminil-Copin, Vincent Tassion, *A new proof of the sharpness of the phase transition for Bernoulli percolation and the Ising model*, Communications in Mathematical Physics 343 (2016), 725–745; arXiv:1502.03050. We use the mean-field lower bound in inverse-temperature form on transitive graphs.
https://arxiv.org/abs/1502.03050

[LS] Russell Lyons, Oded Schramm, *Indistinguishability of Percolation Clusters*, Annals of Probability 27 (1999), 1809–1836; arXiv:math/9811170.
https://arxiv.org/abs/math/9811170

[L] Russell Lyons, *Fixed Price of Groups and Percolation*, arXiv:1109.5418.
https://arxiv.org/abs/1109.5418

[AW] Miklos Abert, Benjamin Weiss, *Bernoulli actions are weakly contained in any free action*, arXiv:1103.1063.
https://arxiv.org/abs/1103.1063
