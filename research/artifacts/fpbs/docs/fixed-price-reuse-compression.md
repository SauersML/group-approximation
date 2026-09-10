# Reuse-information compression for costs of free actions

Research derivation — September 9, 2026

## Status

This note proves a finite-routing compression theorem, a total-variation identity for the conditional traffic penalty, a cost-preserving intermediate-factor construction, and a reduction to adjoining single binary orbit-observables. These are deductions with written proofs; no originality, independent referee verification, or formal verification is claimed. The universal Fixed Price problem and the Benjamini–Schramm conjecture are not proved here.

The central unresolved assertion is still that the extra information can be removed, not merely compressed. Nothing below asserts that the intermediate factor is a proper factor of the source, a finite-fiber extension of the base, or a factor of an iid process. It can retain substantial long-range information.

The proof uses only the basic graphing definition, finite measurable routing, measure-preserving changes of variables, standard factor constructions, and elementary conditional expectation. The Bernoulli application invokes Abért–Weiss. No previous Burnside or small-cancellation class theorem is used.

## 1. Setup

Let Gamma be a finitely generated countably infinite group. Fix a finite generating set S. Let beta be a free p.m.p. action on a standard probability space (Y,nu), alpha a free p.m.p. action on (X,mu), and pi:Y->X a measure-preserving equivariant factor map. Work modulo invariant null sets and use right actions.

Freeness of alpha makes pi a bijection from each beta-orbit onto its image alpha-orbit. A graphing on the base can be split into restrictions of group transformations and lifted without changing its cost or generated connections. Thus

    C(beta) <= C(alpha).

Both costs are finite, bounded above by |S|. Cost is the infimum of the sum of the domain measures of a countable generating graphing.

A finite routing plan consists of:

* finitely many partial transformations phi_j=T_(g_j)|A_j, j=1,...,m;
* a measurable set E_s for each s in S;
* a measurably selected path tau_s(y) from y to ys, for y in E_s, using the phi_j and their inverses;
* one finite upper bound on all path lengths in this plan.

An edge copy is specified by its label j and forward starting point z in A_j. A reverse traversal is charged to that same copy. Repeated group elements among the g_j are permitted and counted as separate graphing copies.

Let N_j(z) be the number of selected path occurrences using edge copy (j,z), where the requests range over sources in z's orbit. It is a bounded nonnegative integer-valued measurable function for each finite plan. To see boundedness, partition request sources by the finitely many possible path words. Each word occurrence is described by an injective partial measure-preserving prefix map, so contributes at most one source to any given edge start. Put N_j=0 off A_j.

For every nonnegative measurable h_j, the exact traffic identity is

    sum_j integral N_j(z) h_j(z) dnu(z)
      = sum_s integral_(E_s) sum_(edge occurrences (j,z) in tau_s(y)) h_j(z) dnu(y).  (1)

It follows by the indicated finite partition and a measure-preserving change of variables at each occurrence.

Write

    r = sum_s nu(Y\E_s),
    B = r + sum_j nu(N_j>0).                                                (2)

Discard unused edge copies, keep all the selected paths, and repair every uncovered request by its direct s-edge. This generates beta at cost at most B, so C(beta)<=B.

Moreover,

    C(beta) = inf_(finite routing plans) B.                                 (3)

For the nontrivial inequality, start with a near-optimal countable generating graphing, split its maps by translating group element, and choose finitely many maps and a finite path bound that cover all but arbitrarily small total measure of S-requests. This is possible because S is finite and every request has a finite path almost surely. Pruning unused edges never increases the graphing cost.

## 2. Audit of conditional traffic descent

Define base-measurable functions

    m_j = E[N_j | pi],
    p_j = P(N_j>0 | pi),
    J_pi = sum_j integral (min(1,m_j)-p_j) dmu.                               (4)

Retain T_(g_j) on K_j={m_j>=1}. If a base s-request remains disconnected, then a lifted source request is either uncovered or its chosen path uses an edge whose projected start is outside K_j. Summing and applying (1),

    sum_s mu(disconnected base s-requests)
      <= r + sum_j integral_(X\K_j) m_j dmu.

Add direct generator edges on those disconnected-request domains. This yields the constructive bound

    C(alpha) <= r + sum_j integral min(1,m_j) dmu = B+J_pi.                   (5)

No independence assumption occurs. This is an upper-bound construction: J_pi is not asserted to be the optimal repair bill for an individual plan.

The exact variational identities are

    C(beta)  = inf B,
    C(alpha) = inf (B+J_pi).                                                (6)

The second identity's reverse inequality follows by lifting near-optimal finite routing plans from alpha. Their traffic is already base measurable, so their J_pi is zero.

Thus

    C(alpha)-C(beta) = inf [B-C(beta)+J_pi],                                 (7)

with both terms inside the brackets nonnegative. Cost equality is equivalent to simultaneous source optimality B->C(beta) and J_pi->0. This equivalence is a characterization, not a proof of the simultaneous approximation.

## 3. Total variation is the exact information loss

Define the finite signed measure

    sigma_j = (N_j-1) nu.

Here ||sigma||_TV means |sigma|(Y), not half this number. Then

    pi_*sigma_j = (m_j-1) mu.

The elementary identity min(1,t)=(1+t-|t-1|)/2 gives

    J_pi = (1/2) sum_j ( ||sigma_j||_TV - ||pi_*sigma_j||_TV ).              (8)

This formula is meaningful because each N_j is bounded. The factor 1/2 is fixed by the identity, not a tunable estimate.

The Jordan decomposition is particularly simple:

    sigma_j^+ = (N_j-1)_+ nu,
    sigma_j^- = 1_(N_j=0) nu.

The negative part is an unused-edge event. The positive part is usage beyond the first request, the source of savings from sharing an edge. Their supports on Y are disjoint.

On X their pushforwards have densities

    a_j = P(N_j=0|pi),
    b_j = E[(N_j-1)_+|pi].

Consequently

    J_pi = sum_j integral min(a_j,b_j) dmu.                                (9)

It is exactly the cancellation between absence and repeated use after projection. Exact traffic magnitude is not required to decide on which side of this cancellation a source point lies.

For intermediate sigma-algebras F subset H, both containing the base information, let J_F and J_H denote (4) with the corresponding conditional expectations. For the same fixed plan,

    J_F-J_H
      = (1/2) sum_j [ ||E[N_j-1|H]||_1 - ||E[N_j-1|F]||_1 ] >= 0.           (10)

The inequality is the L1 contraction of conditional expectation. These increments telescope in an increasing information chain. This does not justify exchanging the optimization over plans with an arbitrary limit; the cost statements below have their own approximation proof.

## 4. Reuse-information compression theorem

For a finite plan define binary observables

    b_j(y)=1_(N_j(y)>=2),       j=1,...,m.                                  (11)

Let Z be the factor generated by the base coordinate pi(y) and all translates

    b_j(yg),       j=1,...,m, g in Gamma.

Concretely, Z is the measured image of

    y -> (pi(y), (b_j(yg))_(j,g))

in X x {0,1}^{m x Gamma}, equipped with the pushforward measure and the induced shift action. This is a standard probability factor because only countably many measurable coordinates are used. Denote the factor maps Y --q--> Z --p--> X. Its action, zeta, is free because alpha is a free factor.

### Theorem 4.1

For every finite routing plan there is a graphing of zeta of cost at most B. In particular,

    C(beta) <= C(zeta) <= B.                                               (12)

### Direct proof

The flags b_j descend to Z. On Z keep T_(g_j) exactly on the domain where b_j=1. Let D_s be the domain on which this retained graphing fails to connect z to zs. Repair it directly with T_s|D_s.

If a source y projects into D_s and y belongs to E_s, its selected route must contain an edge for which b_j=0. If all its edge flags were one, it would project to a retained route.

Since an edge actually used by that route has N_j>=1, such a zero-flag edge has N_j=1. Equation (1) therefore gives

    sum_s mu_Z(D_s) <= r + sum_j nu(N_j=1).

The retained repeated-use edges have cost sum_j nu(N_j>=2), because q preserves measure and their domains are q-measurable. Total cost is at most

    r + sum_j [nu(N_j=1)+nu(N_j>=2)] = B.

The lower bound C(beta)<=C(zeta) is the graphing-lift inequality. QED.

Equivalently, J_q=0: conditional on b_j=0, traffic lies in {0,1}; conditional on b_j=1, traffic is at least two. The projected positive and negative parts in (9) therefore remain disjoint.

### What is actually forgotten

The construction does not need the route chosen for each request, exact traffic magnitudes, or domains of singly used edges as observable data on Z. It retains only repeated-use flags and their group translates. Lost singly used connections are directly repaired, at a cost no larger than the singly used source edges that were discarded.

This is compression, not erasure. The whole orbit-name of even one binary observable can carry complex long-range information. Z->X need not have finite fibers. The invariant measure on the binary coordinates is not asserted independent or Bernoulli. Z need not be a proper factor of Y.

## 5. Exact cost-preserving intermediate factor

### Corollary 5.1

For every epsilon>0 there is an intermediate finite-alphabet extension zeta_epsilon of alpha, factoring beta, such that

    C(beta) <= C(zeta_epsilon) <= C(beta)+epsilon.                           (13)

Here finite-alphabet means finitely many binary orbit-observables, not finitely many points in each factor fiber.

Proof. Choose a finite routing plan with B<=C(beta)+epsilon using (3), then apply Theorem 4.1. QED.

### Corollary 5.2

There exists an intermediate factor zeta, generated over alpha by countably many repeated-use binary observables and their translates, with

    C(zeta)=C(beta).                                                        (14)

Indeed, choose plans D_n with B(D_n)<=C(beta)+1/n and take the factor generated by all their flags. For each n, Theorem 4.1's graphing on that plan's factor lifts to zeta, so C(zeta)<=B(D_n). Also beta factors onto zeta, so C(beta)<=C(zeta). Let n tend to infinity.

One can take increasing finite-alphabet intermediate factors zeta_n (accumulating the first n sets of flags), with

    C(beta) <= C(zeta_n) <= B(D_n),

so their costs converge to C(beta). No general inverse-limit semicontinuity theorem is assumed for this conclusion.

## 6. Localization to a single binary orbit-observable

Suppose a free factor map has a cost drop

    delta=C(alpha)-C(beta)>0.

Choose epsilon in (0,delta). Theorem 4.1 gives m flags and an intermediate factor zeta with C(zeta)<=C(beta)+epsilon. Adjoin their full orbit-names one at a time. Write alpha_0=alpha and alpha_m=zeta. Costs decrease under these extensions, and

    sum_(j=1)^m [C(alpha_(j-1))-C(alpha_j)]
      = C(alpha)-C(zeta) >= delta-epsilon.

Hence at least one step satisfies

    C(alpha_(j-1))-C(alpha_j) >= (delta-epsilon)/m.                           (15)

Each step adjoins one binary observable together with all its translates; all actions remain free.

Thus for a finitely generated group, the following are equivalent:

(A) all free p.m.p. actions have the same cost;
(B) no extension of a free p.m.p. action formed by adjoining the orbit-name of one binary observable has smaller cost;
(C) every free factor map admits source-near-optimal finite routing plans whose signed traffic measures lose asymptotically zero total variation under projection.

(A)->(B) is immediate. (B) plus the finite-alphabet approximation proves factor invariance. Apply factor invariance to the two projections from the product of arbitrary free actions to get (A). Equivalence with (C) is (7)-(8).

This is an exact reduction, not a proof of (B). A binary observable is not the same as a single independent coin or a two-point fiber extension.

## 7. The still-unproved step

To deduce Fixed Price one needs, for every free factor map pi, plans D_n with

    B(D_n)->C(beta),
    sum_j ( ||(N_(j,n)-1)nu||_TV
             - ||pi_*((N_(j,n)-1)nu)||_TV )->0.                              (16)

The compression theorem proves (16) after replacing pi by a generally more informative intermediate factor. It does not prove (16) for the original pi.

Equivalently, the missing construction must make the pushforwards of the unused-edge measures and the repeated-use measures asymptotically singular while preserving the near-optimal total edge budget. No implication from freeness alone to this alignment is established here. Treating conditional Jensen's inequality as equality, or declaring the flags to be target measurable, would simply assume the missing statement.

For a finitely generated group, Abért–Weiss gives maximal cost to Bernoulli actions. For a free action a, take beta=a x b and alpha=b. Then C(beta)<=C(a)<=C(b). Proving (16) for these projections would give equality and settle the finitely generated case. The theorem does not supply it.

The full countable-group formulation includes infinite generating sets and potentially infinite cost. Finite-demand approximations used here do not silently cover that additional scope. No Bernoulli-percolation bound or full solution of Benjamini–Schramm is deduced.

## 8. Verification boundaries

The script verify_reuse_compression.py uses only Python's standard library and exact Fraction arithmetic. It checks:

* total-variation, overlap, and positive-sign refinement identities for 3,840 weighted finite traffic/partition cases;
* the information-chain identity for 15,360 nested-information cases;
* the actual retained-reused-edge plus repair construction on all 4,096 pairs of domains for two group-labeled maps on a six-point, two-sheet free C3-action.

In the last tests the intermediate factor is generated by the base and all translates of the reuse flags. This tests the equivariant construction, not only the scalar formula.

These are finite checks. They do not prove measurable approximation, the universal alignment assertion, novelty, or either conjecture. No formal theorem prover or independent review has been used. No Cairn status change for the universal goals is claimed.

## References and provenance

The predecessor is the conversation note fixed-price-conditional-traffic.md. Sections 1-2 above reprove the parts used; the total-variation identities and reuse-information construction are given in full here.

[G] Damien Gaboriau, Around the orbit equivalence theory, measure equivalence, cost and l2 Betti numbers, author-hosted lecture notes dated October 3, 2025. Definitions of cost and Proposition 2.39 (relative cost). Author copy:
https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf

[AW] Miklos Abert and Benjamin Weiss, Bernoulli actions are weakly contained in any free action, arXiv:1103.1063v2. Corollary 2 gives Bernoulli maximality for finitely generated groups. Used only for the application in Section 7:
https://arxiv.org/html/1103.1063v2

[TD] Robin Tucker-Drob, Shift-minimal groups, fixed price 1, and the unique trace property, arXiv:1211.6395v3. Section 6 discusses cost and pseudocost; context for the countable-group limitation, not a premise of the finite-routing proof:
https://arxiv.org/html/1211.6395v3
