# Factor descent, shared connections, and conditional routing traffic

Research derivation — September 9, 2026

## Status

This note proves a constructive cost-descent inequality and an exact variational
characterization of cost preservation under a factor map between free p.m.p.
actions of a finitely generated group. It does not prove that every such factor
preserves cost. Therefore it does not solve Fixed Price or Benjamini–Schramm.
No novelty, independent verification, or formal verification is claimed.

The argument does not use the earlier Burnside, small-cancellation, or
finite-priority class claims. Its inputs are the definitions of cost,
measure-preserving changes of variables, conditional expectation, and, for the
optional relative version, standard hyperfinite and relative-cost facts.

The central distinction is between paying once for an edge and paying separately
for each connection request that uses it. Forgetting an extra coordinate can
mix absence of an edge with repeated use of that edge. The exact penalty of a
particular constructive descent procedure is a conditional clipping/Jensen gap.
Taking the infimum over all finite routing plans gives exact action costs.

## 1. Actions and factors

Let Gamma be finitely generated, and fix a finite generating set S. It need not
be symmetric: paths may traverse graphing edges in either direction. Let beta
be a free p.m.p. action on a standard probability space (Y,nu), and let alpha be
a free p.m.p. action on (X,mu). Let

    pi:Y -> X

be a measure-preserving equivariant factor map. Remove invariant null sets so
that the relevant identities and freeness hold pointwise. Use right notation
`y -> yg` and `x -> xg`.

Freeness of alpha makes pi bijective on each individual beta-orbit: points yg
and yh have the same projection only if g=h. The full fiber pi^{-1}(x) can of
course contain many points, in different beta-orbits.

Any graphing of alpha can be split into restrictions of group transformations
and lifted to beta with the same cost. Freeness ensures that a base path ending
at xg lifts to a path ending at yg, not merely at some point projecting to xg.
Consequently

    C(beta) <= C(alpha).                                      (1.1)

For a fixed group, equality for all such free factor maps is equivalent to
Fixed Price: apply factor invariance to both projections from the product of
any two free actions. This equivalence does not require finite generation, but
the finite routing characterization below does.

## 2. Finite routing plans

A plan D consists of the following data on Y.

1. A finite partial graphing Phi=(phi_1,...,phi_m), where

       phi_j = T_{g_j}|A_j,   g_j in Gamma,   A_j measurable.

   This graphing is not required to generate beta. Repetitions among the g_j
   are allowed; graphing copies are counted separately.

2. For each s in S, a measurable set E_s and, for each y in E_s, a chosen
   Phi-path tau_s(y) from y to ys. For this plan the lengths have one finite
   upper bound L. The path choice is measurable. For instance one can order
   the finitely many words in Phi^{+/-1} of length <=L and take the first valid
   word with the correct endpoint.

Define the uncovered-demand budget

    r(D) = sum_{s in S} nu(Y \ E_s).                          (2.1)

An edge copy is identified by (j,z), with z in A_j and endpoints z,zg_j.
A reverse traversal still uses the edge copy whose forward starting point is z.
Define its traffic

    k_j(z) = number of chosen requests (s,y) whose route uses
             the edge copy (j,z), counted with multiplicity.   (2.2)

The source y in (2.2) ranges over the orbit of z. These are integer counts,
not unnormalized measures of individual points. They are measurable and bounded
for a fixed finite plan: there are finitely many path words and occurrences;
each prefix map is an injective partial p.m.p. transformation, so it contributes
at most one possible source to a given edge-starting point. Also k_j=0 off A_j.

The elementary change-of-variables identity is, for nonnegative measurable f_j,

    sum_j integral_Y k_j(z) f_j(z) dnu(z)
      = sum_s integral_{E_s}
            sum_{edge occurrences (j,z) in tau_s(y)} f_j(z)
        dnu(y).                                               (2.3)

To prove it, partition E_s by its chosen finite path word. At each occurrence,
change variables from the source to the forward starting point of that edge.
The corresponding prefix, including a reverse step when needed, is a partial
p.m.p. bijection. Sum the resulting identities.

Let

    U_j={z:k_j(z)>0},
    B(D)=sum_j nu(U_j)+r(D).                                  (2.4)

Discard every unused edge copy, then add T_s on Y\E_s for each s. All covered
requests retain their paths; all uncovered ones get a direct edge. Thus

    C(beta) <= B(D).                                          (2.5)

B is a valid full source budget. It is not claimed to equal the cost of a
particular completed graphing, since coinciding domains might be merged.

## 3. Conditional traffic and the exact scalar penalty

Disintegrate nu over pi, or equivalently use conditional expectation onto the
sigma-algebra pi^{-1}(B_X). Define functions on X by

    m_j(x) = E_nu[k_j | pi=x],
    p_j(x) = P_nu(k_j>0 | pi=x).                              (3.1)

Here m_j is mean traffic and p_j is the conditional fraction of fibers in which
the edge copy is used. They satisfy m_j>=p_j.

Put psi(t)=min(1,t), and define

    J_pi(D) = sum_j integral_X [psi(m_j(x))-p_j(x)] dmu(x).
                                                                    (3.2)

Since k_j is a nonnegative integer, psi(k_j)=1_{k_j>0}. Concavity of psi gives

    psi(E[k_j|pi]) >= E[psi(k_j)|pi],

so J_pi(D)>=0. More explicitly,

    psi(m_j)-p_j
       = min(1-p_j, m_j-p_j)
       = min(P(k_j=0|pi), E[(k_j-1)_+|pi]).                   (3.3)

No tunable threshold is hidden here. The number 1 is the unit cost of retaining
one partial-transformation edge at a base point. It is compared with the cost
of separately repairing the requests that used it.

A useful interpretation: after projection, the two nonnegative measures

    pi_*(1_{k_j=0} nu),    pi_*((k_j-1)_+ nu)

have densities 1-p_j and m_j-p_j. The integral in (3.3) is their overlap.
On Y these two measures are supported on disjoint sets. Projection can make
their images overlap. This is an exact measure-theoretic formulation, not a
claim that entropy or independence of every graphing label must be preserved.

## 4. Constructive descent theorem

**Theorem 4.1.** For every finite routing plan D,

    C(alpha) <= B(D)+J_pi(D)
              = r(D)+sum_j integral_X min(1,m_j(x)) dmu(x).    (4.1)

**Proof.** Define

    K_j={x:m_j(x)>=1},

and on X retain the partial transformation T_{g_j}|K_j. Call their graphing Psi.
Let D_s be the measurable set of x for which x and xs are not Psi-connected.
Add T_s|D_s, so the completed graphing generates alpha.

If pi(y) belongs to D_s and y belongs to E_s, the chosen source path tau_s(y)
must encounter an edge copy (j,z) with pi(z) outside K_j. Otherwise its projection
would be a Psi-path from pi(y) to pi(y)s, a contradiction. Hence (2.3) gives

    sum_s mu(D_s)
      <= r(D) + sum_j integral_Y k_j(z) 1_{pi(z) notin K_j} dnu(z)
       = r(D) + sum_j integral_{X\K_j} m_j(x) dmu(x).          (4.2)

The total base graphing cost is at most

    sum_j mu(K_j)+sum_s mu(D_s)
      <= r(D)+sum_j integral_X [1_{m_j>=1}+m_j 1_{m_j<1}] dmu
       = r(D)+sum_j integral_X min(1,m_j) dmu.

Finally sum_j integral p_j = sum_j nu(U_j), giving (4.1). QED.

There is no use of independent edge sampling, no assumption of independence
between route failures, and no multiplicative maximum-route-length error term.
Routes are finite and their traffic is explicitly charged. Long routes can of
course cause repeated traffic; the theorem does not claim otherwise.

The sets K_j and D_s are in the target action. The construction genuinely gives
a base graphing rather than a graphing on an auxiliary extension.

## 5. Exact variational formulas

Let P denote all finite routing plans of Section 2.

**Theorem 5.1.**

    C(beta)  = inf_{D in P} B(D),
    C(alpha) = inf_{D in P} [B(D)+J_pi(D)].                     (5.1)

**First formula.** Inequality (2.5) is one direction. For the other, take a
countable generating graphing of beta with cost within epsilon of C(beta),
and split its maps into restrictions of group elements without changing cost.
Every s-request has a finite path almost surely. Taking a sufficiently large
finite subgraphing and sufficiently large finite path-length bound makes r(D)
as small as desired, since S is finite. Chosen used edges are a subset of the
finite graphing, so B(D) approaches C(beta) from above.

**Second formula.** Theorem 4.1 is one direction. Conversely, take a near-optimal
countable graphing of alpha and approximate its requests by a finite graphing
and finite paths in the same way. Lift this finite plan through pi. Because pi
is orbitwise bijective and the lifted decisions depend only on x, its traffic
is also lifted from the base:

    k_j(y)=bar_k_j(pi(y)).

Thus m_j=bar_k_j and p_j=1_{bar_k_j>0}; integer traffic implies J_pi=0.
The lifted B equals the base used-edge-plus-repair budget, which approaches
C(alpha). QED.

Consequently,

    C(alpha)-C(beta)
      = inf_D [(B(D)-C(beta))+J_pi(D)].                        (5.2)

Both terms inside the brackets are nonnegative. Therefore:

**Corollary 5.2 (exact no-loss criterion).**

    C(alpha)=C(beta)

if and only if there is a sequence D_n such that

    B(D_n) -> C(beta),     J_pi(D_n) -> 0.                     (5.3)

One must achieve these limits simultaneously. The existence of plans with
J=0 alone is automatic by lifting target plans; their source budgets may be
larger than the source optimum. Source optimality alone need not control J.

The equivalence is not a proof that the plans in (5.3) always exist. The useful
extra content is the explicit target graphing and the scalar nonnegative
quantity whose smallness suffices.

## 6. Exact positive no-loss situations

For a particular j and almost every x, (3.3) vanishes if either:

- k_j>=1 on almost every conditional fiber point (p_j=1); or
- k_j belongs to {0,1} on almost every conditional fiber point (m_j=p_j).

The choice of the alternative may depend on j and x. Conversely, since traffic
is integer-valued, zero defect implies at least one of these alternatives.

Thus uncertain one-use edges can be discarded and their requests directly
repaired without any increase in the budget. Repeatedly used edges can also
descend without loss when they are used on essentially every fiber. What
produces a positive defect is mixing absence with multiple use at the same
projected point and edge label.

For example, an edge used exactly once on an arbitrary conditional fraction p
of the fiber has defect p-p=0; the value of p need not be close to zero or one.
If it is used k>=2 times on a fraction p and is unused otherwise, its local
penalty is exactly min(1-p,(k-1)p). These are evaluations of the formula, not
counterexamples to Fixed Price or assertions of action realizations.

## 7. Removing the universal cost-one baseline

The standard relative-cost theorem [G, Proposition 2.39] states that for an
aperiodic subrelation S<=R,

    C(R)-C(S) <= relC(R;S) <= C(R)-1.

In particular if C(S)=1,

    relC(R;S)=C(R)-1.                                        (7.1)

A short explanation of the upper bound is that an arbitrarily small complete
section A for S is also complete for R, S joined with R|A generates R, and cost
induction gives unnormalized cost C_mu(R|A)=C(R)-1+mu(A). The lower bound follows
by appending the relative graphing to a near-optimal S-graphing.

Suppose S on X is aperiodic hyperfinite. Its orbitwise lift is

    S^pi = {(y,yg): (pi(y),pi(y)g) belongs to S}.

It is again aperiodic hyperfinite: finite-class approximants to S lift to
finite-class approximants with exactly the same class cardinalities, because
pi is orbitwise bijective. Thus C(S)=C(S^pi)=1.

Allow the routing plans to use lifted S-steps without charging their traffic;
charge only additional group-labeled partial maps. All proofs above go through.
One can fix a countable graphing of S, lift it, and use finitely many of its maps
in any given finite plan, so bounded measurable traffic remains well defined.
The exact relative formulas are

    C(beta)-1  = inf_D B_S(D),
    C(alpha)-1 = inf_D [B_S(D)+J_pi,S(D)].                      (7.2)

Here B_S charges only used added edges and uncovered generator requests. Near-
optimal relative graphings and finite path approximation prove exactness;
lifting near-optimal target relative plans proves the opposite direction.

For the nonamenable Bernoulli target, such a spine is available from the
Gaboriau–Lyons free F2 subrelation [GL]: take the infinite cyclic subrelation
of one of its free generators. For amenable groups the fixed-price-one result
is already a standard input. No small-cancellation presentation is needed.

## 8. Precise relation to Fixed Price

For a finitely generated Gamma, Abért–Weiss [AW] makes a Bernoulli action b a
maximum-cost free action. For any free a, form beta=a times b and project to
alpha=b. Pullback through the other projection gives

    C(a times b) <= C(a) <= C(b).

Thus cost-preserving descent for this one class of projections would prove
Fixed Price for finitely generated groups. In the language of (5.3), what is
still needed is a theorem producing source-near-optimal routing plans with
vanishing J for these projections. The present note does not prove that.

The full countable-group problem includes infinite generating sets and
potentially infinite costs. This finite-demand variational proof is not silently
extended to that setting. Standard pseudocost literature [TD] explains why
exhaustions require care. A proof for all finitely generated groups would not be
asserted here to settle all those additional cases without an argument.

No Bernoulli percolation threshold inequality is obtained. The cost problem
and the percolation problem impose different constraints; the source-to-target
rounding here is not independent bond percolation.

## 9. Verification boundaries

The script check_descent.py tests the actual constructive bound and its traffic
identities on every pair of partial domains for the +1 and -1 maps on the
six-point two-sheet extension of the regular C3 action. It checks the graphings
before and after projection, exact conditional means, the min formula, direct
repairs, and the source used-edge pruning.

All 4,096 configurations passed. This validates finite accounting only, not
measurability, the variational approximation, any external theorem, or Fixed
Price. No Cairn compilation or previous class theorem is used as mathematical
validation of this note.

## References

[G] Damien Gaboriau, Lectures on Orbit Equivalence, Measure Equivalence and Cost.
Propositions 2.33 and 2.39 (complete-section induction and relative cost).
https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf

[AW] Miklós Abért and Benjamin Weiss, Bernoulli actions are weakly contained in
any free action, arXiv:1103.1063v2, Corollary 2 and Theorem 9.
https://arxiv.org/html/1103.1063v2

[GL] Damien Gaboriau and Russell Lyons, A Measurable-Group-Theoretic Solution to
von Neumann's Problem, arXiv:0711.1643v2, Theorem 1.
https://arxiv.org/html/0711.1643v2

[TD] Robin Tucker-Drob, Shift-minimal groups, fixed price 1, and the unique trace
property, arXiv:1211.6395v3, Section 6 and the cost/pseudocost discussion.
https://arxiv.org/html/1211.6395v3
