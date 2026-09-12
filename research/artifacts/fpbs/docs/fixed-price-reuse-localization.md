# Reuse decisions, Bernoulli information, and the unresolved cost-descent step

Research continuation — September 9, 2026

## Status

This note does not solve universal Fixed Price or Benjamini–Schramm. It proves a finite-observable localization consequence of the previous conditional-traffic inequality and gives a direct proof of the known fact that adding independent Bernoulli information to a free action of a finitely generated group does not change its cost. The latter fact belongs to the established weak-containment theory, not to a new discovery here. The localization statements are written deductions; no priority or independent-validation claim is made.

Only the conditional-traffic construction is used from the earlier conversation, and its necessary argument is repeated below. Earlier small-cancellation, Burnside, and class-level claims are not premises.

All actions are essentially free probability-preserving actions of a fixed countably infinite, finitely generated group Gamma on standard probability spaces. Null sets are discarded invariantly. Right-action notation is used. Write C_X for the cost of an action on X. Finitely many full generator transformations give a finite upper bound for these costs.

## 1. Factor maps and finite routing plans

Let pi:(Y,nu)->(X,mu) be a measure-preserving equivariant factor map, with both actions free. It is bijective from each individual Y-orbit onto an X-orbit. A graphing on X lifts to a generating graphing on Y of the same cost. Thus C_Y<=C_X.

Fix a finite generating set S of Gamma. A finite routing plan on Y consists of finitely many partial transformations

    phi_j = T_(g_j)|A_j,  1<=j<=m,

and, for each s in S, chosen paths of one finite bounded length from y to ys on a measurable set E_s. The rest of the s-requests are left uncovered. Paths are measurable, for example by taking the first valid word in a finite list. An edge COPY is (j,z), where z is the forward starting point; a reverse use is charged to that same copy.

Let N_j(z) be the number of occurrences of this copy in all chosen requests from roots in the orbit of z. For a fixed finite plan these functions are measurable, nonnegative, integer-valued, and bounded. Indeed, there are finitely many path words and edge occurrences, and each prefix is a partial measure-preserving bijection. Each prefix contributes at most one possible source to a specified edge-starting point.

Put

    r = sum_(s in S) nu(Y\E_s),
    B = r + sum_j nu{N_j>0}.

Discarding unused copies and adding direct edges for uncovered requests generates the source action. Hence C_Y<=B. Moreover,

    inf_(finite plans) B = C_Y.                              (1)

For the converse approximation, start with a nearly optimal countable graphing, split its maps into restrictions of group transformations, truncate it, and bound path lengths. Every generator connection has a finite path almost surely. Since S is finite, the total uncovered measure tends to zero as the finite graphing and path cutoff increase. The retained used copies are a subset of the starting graphing. This proves (1).

For nonnegative f_j the following traffic-accounting identity is useful:

    sum_j integral N_j(z) f_j(z) dnu(z)
      = sum_s integral_(E_s) sum_(edge occurrences (j,z) in the chosen path)
                           f_j(z) dnu(y).                    (2)

Partition E_s according to its path word and change variables at each occurrence from y to the forward starting point z. Each prefix map is an injective partial p.m.p. map. Summing proves (2).

## 2. The descent inequality, with proof

For the factor map pi define

    m_j(x)=E[N_j|pi=x],
    p_j(x)=P(N_j>0|pi=x),
    psi(t)=min(1,t),
    J_pi=sum_j integral [psi(m_j)-p_j] dmu.

Since N_j is an integer, psi(N_j)=1_{N_j>0}. Conditional Jensen gives J_pi>=0. Pointwise,

    psi(m_j)-p_j
      = min(1-p_j,m_j-p_j)
      = min(P(N_j=0|pi),E[(N_j-1)_+|pi]).                    (3)

Keep T_(g_j) on K_j={m_j>=1} in the base action. Let D_s be the base points whose s-request is not connected by these retained maps. If pi(y) lies in D_s, then either y was an uncovered source request, or its chosen route uses an edge copy (j,z) with pi(z) not in K_j. Otherwise the route would project to a retained base path.

Using (2),

    sum_s mu(D_s)
      <= r + sum_j integral_(X\K_j) m_j dmu.

Add the direct s-edges on D_s. The resulting base graphing generates and costs at most

    r + sum_j integral min(1,m_j) dmu = B+J_pi.

Therefore

    C_X <= B+J_pi.                                          (4)

Equation (4) is a constructive bound, not an identity for every plan. Its optimization is exact:

    C_X = inf_(finite source plans) (B+J_pi).                 (5)

To prove the opposite inequality, lift finite approximations of nearly optimal base graphings and their paths. Lifted traffic is measurable in the base and integer-valued, so J_pi=0. This establishes (5).

Thus cost preservation is equivalent to the simultaneous existence of plans with B->C_Y and J_pi->0. No part of this note assumes that simultaneous approximation for all factor maps.

## 3. A finite collection of reuse indicators captures nearly optimal cost

### Theorem A

For every epsilon>0, there are finitely many measurable sets B_1,...,B_m in Y and an intermediate factor

    Y -> Z -> X

such that Z is generated over X by the full Gamma-orbit names of these binary observables, and

    C_Y <= C_Z < C_Y+epsilon.                                (6)

The observables can specifically be chosen as

    B_j={N_j>=2}                                             (7)

for one finite source routing plan with budget B<C_Y+epsilon. In particular

    sum_j nu(B_j) <= sum_j nu{N_j>0} <= B.                    (8)

### Proof

Choose the finite plan by (1). Let the sigma-algebra for Z be generated by pi^{-1}(B_X) and all translates of the B_j. This is a countably generated invariant sigma-algebra and has a standard probability factor model. Concretely, use the pushforward of

    y -> (pi(y), (1_(B_j)(yg))_(j,g))

into X times {0,1}^{m x Gamma}. The intermediate action is free because it still factors onto the free X-action.

Condition traffic on Z. On B_j the conditional traffic is always at least two, so p_j=1 and psi(m_j)=1. On the complement, traffic belongs to {0,1}, so m_j=p_j and psi(m_j)=p_j. Hence the conditional traffic penalty for Y->Z is exactly zero, at every edge copy almost everywhere.

Apply (4) to Y->Z. This gives C_Z<=B<C_Y+epsilon. The factor inequality gives C_Y<=C_Z. QED.

Only the reuse classification is revealed. Source domains, full traffic values, and routes need not be measurable in Z. The target graphing is produced by the descent construction.

This is not the claim that a bit at one root encodes the source action. We retain all Gamma-translates of finitely many bits. Each resulting symbolic process can have arbitrarily complicated long-range constraints.

## 4. A single binary symbolic extension suffices to witness a cost drop

### Corollary B

Suppose C_Y<C_X. Then there are free intermediate factors

    Y -> Z' -> Z -> X

such that C_(Z')<C_Z and the sigma-algebra of Z' is generated over Z by the Gamma-translates of ONE measurable set.

### Proof

Choose epsilon<C_X-C_Y in Theorem A, so C_Zm<C_X for the final finite-observable factor. Adjoin its indicators one at a time to form

    X=Z_0 <- Z_1 <- ... <- Z_m.

The costs are nonincreasing and the last is strictly smaller than the first. At least one successive factor map has a strict decrease. QED.

Consequently, for a fixed finitely generated Gamma, the following assertions are equivalent:

1. all free p.m.p. Gamma-actions have the same cost;
2. every factor map between free Gamma-actions preserves cost;
3. every factor map between free Gamma-actions whose source is generated over its target by one binary orbit observable preserves cost.

Only 3=>2 needs the corollary; 2=>1 follows from the two projections of the product of arbitrary free actions. This is a reduction, not a proof of assertion 3. A binary SYMBOLIC extension can have infinite or uncountable fibers; it is not a two-point fiber extension.

## 5. An unconditional positive theorem: independent Bernoulli information is removable

### Theorem C (known consequence of weak-containment theory)

If b is a Bernoulli shift and a is a free action of a finitely generated group, then

    C(a x b)=C(a).                                          (9)

Every intermediate factor a x b -> z -> a has the same cost as well. This holds for arbitrary measurable relative factors of iid, not just finite-radius codes.

The weak equivalence a x b~a is established in the literature; see [Sew, Section 5], which explicitly attributes the stabilizer-preserving version to Tucker-Drob and gives a joining-relative version in Lemma 5.1. Cost monotonicity for weak containment is [AW, Theorem 9]. A direct cost proof is given here to isolate the mechanism.

### Finite conditional-noise simulation

Let F be a finite subset of Gamma, K a finite alphabet with distribution lambda, and h:X x K^F->[0,M] be measurable. For every delta>0 there is a measurable coloring c:X->K such that

    integral h(x,(c(xg))_(g in F)) dmu(x)
       <= integral integral h(x,z) d(lambda^F)(z) dmu(x)+delta. (10)

To prove this, choose a finite measurable partition separating xg for g in F outside a set of measure less than delta/M (the M=0 case is trivial). Give its atoms independent lambda-colors. At a good root x the tested colors are independent, while all the pre-existing base data in h remain fixed. Hence the expected score is exactly the right conditional product average. Bad roots contribute at most M each. Integrate and average to obtain one deterministic coloring.

### Apply the simulation to graphing cost plus repairs

Let Phi be a finite partial graphing on a x b, with fixed group labels, and fix a path cutoff L. Define its score as graphing cost plus the total measures of generator pairs not connected within L. This score upper-bounds the action cost, because adding direct edges on the failure sets makes it generating.

Starting with a nearly optimal countable generating graphing on a x b, truncate to finitely many maps and sufficiently large L; the score approaches C(a x b). This is the same finite-graphing-plus-repair approximation as (1), or the formulation in [TD, Lemma 6.2].

Approximate the finitely many domains, in product measure, by sets depending on the base x and only finitely many Bernoulli coordinates, with those coordinates quantized to a finite alphabet. This is ordinary cylinder approximation with coefficients measurable on X. The score changes by arbitrarily little: whether a bounded path is valid tests finitely many translated domains, and a finite union bound controls all changes.

For the resulting graphing, its pointwise edge-count-plus-failure score is h(x,z|F) as in (10). Apply (10) to obtain a deterministic coloring on X. The local construction now defines genuine partial group transformations on X. Repair the finitely many remaining generator failure sets. Its cost is at most the source score plus the arbitrary simulation and approximation errors. Thus C(a)<=C(a x b).

The reverse inequality follows by lifting a graphing from a. This proves (9). For an intermediate factor, use

    C(a x b)<=C(z)<=C(a).

QED.

The proof works because the added coordinates are conditionally independent once x is fixed. It does not sample arbitrary group-coherent source states independently at different vertices. Such sampling need not define the original extension or preserve its routing certificates.

## 6. A sparse version near cost one

Assume the base relation has a fixed aperiodic hyperfinite subrelation H. Lift H orbitwise to every extension above X. The lift is again aperiodic hyperfinite: finite-class approximants lift with exactly the same class sizes because factor maps are orbitwise bijective.

For such H, the established relative-cost formula is

    relC(R;H)=C(R)-1.                                       (11)

See [G, Proposition 2.39], visually verified together with the induction formula on PDF page 15 and its proof on PDF page 16. Existence of a suitable H in the nonamenable Bernoulli base, for example, follows from the cyclic subrelation of the Gaboriau-Lyons free F2-subaction [GL].

Use finite routing plans with lifted H-steps available at no additional charge; only added edges have traffic counted. For a fixed plan take finitely many maps from a fixed countable graphing of H as needed, so the traffic functions remain measurable and bounded. The proofs of (2)-(5) remain valid for relative budgets. Finite approximations of near-optimal relative graphings give

    inf B_H=C_Y-1.

### Corollary D

For every epsilon>0, there is an intermediate finite-observable factor Z as in Theorem A such that

    C_Z<C_Y+epsilon,
    sum_j nu(B_j)<C_Y-1+epsilon.                             (12)

If C_Y=1 this says that a factor of cost below 1+epsilon can be captured over the base by a finite-valued signal Theta=(1_(B_1),...,1_(B_m)) satisfying

    nu{Theta != (0,...,0)}<epsilon.                          (13)

### Proof

Take a relative finite plan with B_H<C_Y-1+epsilon. Reveal B_j={N_j>=2}; the relative traffic defect is zero. The relative descent theorem gives relC(R_Z;H^Z)<=B_H, and (11) yields C_Z<=1+B_H. Since B_j is contained in the used domain of added edge j, its measure is at most that domain's measure. Summing proves (12) and the union bound proves (13). QED.

This does not show the rare signal can be discarded for negligible cost. Its alphabet size and routing multiplicities are not uniformly bounded. A single request may use long paths, and a rarely present connector may serve many requests.

One exact warning, without an example or guessed constant: if C_Y=1, C_X=1+Delta, a relative plan has budget b, and all its added-edge traffics are bounded by K, then

    J_pi <= sum_j E[(N_j-1)_+] <= (K-1)b,
    Delta <= b+J_pi <= Kb.                                 (14)

Thus any hypothetical positive gap would force K>=Delta/b along vanishing relative budgets. Equation (14) does not prove such a gap exists or that K has a uniform upper bound.

## 7. What remains unresolved

For a free a and Bernoulli b, Theorem C strengthens the comparison to

    C(a x b)=C(a)<=C(b).

The first projection, forgetting Bernoulli information, preserves cost. The other projection a x b->b forgets the whole a-process. Applying Theorem C to that projection would confuse independence between the two probability-space coordinates with independence of the orbit labels in a. The latter is not available for an arbitrary a.

The localization theorem says that any possible gap in that second projection is already witnessed through finitely many binary reuse processes, and through a single binary extension at some intermediate step. It does not prove those processes can be simulated over the Bernoulli base while keeping source optimality.

The missing mathematical statement remains: source-near-optimal routing plans can be chosen with vanishing conditional traffic penalty for the projection a x b->b. Equivalently, one must establish cost preservation for all free binary symbolic extensions. Neither nonnegative Jensen gaps, finite alphabets, martingale convergence for a FIXED plan, nor small measure of the reuse signal proves that simultaneous optimization.

If this statement were proved for all finitely generated groups, Fixed Price for those groups would follow. The general countable case still requires appropriate treatment of infinitely many demands and possibly infinite cost, rather than a silent extrapolation; [TD] explains the cost/pseudocost issue. No independent percolation threshold statement has been deduced here.

## References and attribution

[AW] Miklos Abert and Benjamin Weiss, *Bernoulli actions are weakly contained in any free action*, arXiv:1103.1063v2. Theorem 9 gives cost monotonicity for weak containment; Corollary 2 gives Bernoulli maximality for finitely generated groups.
https://arxiv.org/html/1103.1063v2

[Sew] Brandon Seward, *Weak containment and Rokhlin entropy*, arXiv:1602.06680v2. Section 5 explicitly discusses weak equivalence to a stabilizer-preserving Bernoulli extension; Lemma 5.1 proves the joining-relative form.
https://arxiv.org/html/1602.06680v2

[G] Damien Gaboriau, *Around the orbit equivalence theory, measure equivalence, cost and l2 Betti numbers*, author-hosted lecture notes dated October 3, 2025. Propositions 2.33 and 2.39.
https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf

[TD] Robin Tucker-Drob, *Shift-minimal groups, fixed price 1, and the unique trace property*, arXiv:1211.6395v3. Lemma 6.2 (finite graphing plus repairs), Corollary 6.5 and the cost/pseudocost discussion.
https://arxiv.org/html/1211.6395v3

[GL] Damien Gaboriau and Russell Lyons, *A Measurable-Group-Theoretic Solution to von Neumann's Problem*, arXiv:0711.1643v2, Theorem 1.
https://arxiv.org/html/0711.1643v2

Prior conversation note: fixed-price-conditional-traffic.md. Its finite traffic and descent arguments are repeated in Sections 1-2. The localization and sparse-decision deductions are not attributed to an unlocated published theorem and are not claimed novel.

No numerical experiment or dependency-graph compilation is offered as evidence for the unresolved universal statement.
