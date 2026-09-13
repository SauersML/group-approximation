# Binary reuse entropy needs a traffic-tail estimate

September 12, 2026. A written quantitative deduction and an exact countermodel
for the live factor-descent programme. This does not settle Fixed Price, prove
universal traffic compactness, or invalidate the existing conditional-traffic
variational theorem. No mathematical priority or formal verification is claimed.

## 1. Quantitative positive criterion

Use a finite routing plan D and factor pi:Y->X as in
`fixed-price-conditional-traffic.md`. Its edge-copy traffic is k_j, its completed
source budget is B(D), and its conditional clipping defect is J_pi(D). Write

    F_j = 1_{k_j >= 2},       Q_j = (k_j-1)_+,
    t_j(x) = E[F_j | pi=x],
    H_pi(D) = sum_j integral h(t_j(x)) dmu(x),
    h(t) = -t log(t) - (1-t) log(1-t),
    Tail_T(D) = sum_j integral Q_j 1_{Q_j>T} dnu.

Logs are natural, with 0 log 0=0. H is the **sum of the conditional Shannon
entropies of every individual reuse flag**, integrated over the base. It is
not entropy per edge, divided by plan size, entropy rate, or the entropy of
only selected flags. It can exceed the joint one-site flag entropy.

For every T>=1,

    J_pi(D) <= T H_pi(D)/(2 log 2) + Tail_T(D).              (1)

To prove this, work at one edge copy and base point, and put

    a = P(k=0 | x),       r = E[Q | x],       t=P(k>=2 | x).

The exact scalar defect is min(a,r). Predict the reuse flag by 1_{t>=1/2}.
If t>=1/2, then min(a,r)<=a<=1-t. If t<1/2, then

    min(a,r) <= r <= T t + E[Q 1_{Q>T} | x].

Thus in both cases it is at most

    T min(t,1-t) + E[Q 1_{Q>T} | x].

Concavity of binary entropy on each half of [0,1] gives
h(t)>=2(log 2)min(t,1-t): use the chords from 0 to 1/2 and from 1/2 to 1.
Integrate and sum over all edge copies to obtain (1).

Consequently, for a finite-cost base factor, the established constructive
traffic theorem gives

    C(X) <= B(D) + T H_pi(D)/(2 log 2) + Tail_T(D).          (2)

For countable groups this uses the finite-prefix demand convention with the
entire unprocessed base graphing tail included in B(D). No entropy is charged
to that deterministic base repair tail.

In particular, suppose B(D_n)->C(Y), H_pi(D_n)->0, and the repeated traffic is
uniformly integrable across the disjoint unions of edge-copy spaces:

    lim_{T->infinity} sup_n Tail_T(D_n) = 0.                (3)

First choose T using (3), then n using vanishing entropy; (1) gives J_pi(D_n)->0,
and (2) gives C(X)=C(Y). More generally it suffices to choose T_n>=1 with
T_n H_pi(D_n)->0 and Tail_{T_n}(D_n)->0. This latter sufficient condition permits
plans whose traffic bounds grow without a common uniform-integrability bound.
None of these hypotheses is established for arbitrary near-optimal plans.

## 2. One fixed free factor and exactly optimal plans

Let X={0,1}^Z carry the fair Bernoulli shift sigma and let Z_2 denote the compact
group of 2-adic integers with Haar probability. Let

    Y=X x Z_2,       T(x,u)=(sigma x,u+1),       pi(x,u)=x.

Both actions are essentially free. For the base, the fixed set of any nonzero
shift is null because infinitely many independent coordinates must agree.
The product is therefore free as well. Both costs are exactly one: the full
single-generator graphing costs one, and every aperiodic p.m.p. relation has
cost at least one. No finite-index cost formula is needed.

For n>=2 put q=2^n, L=q/2, and let rho(u) in {0,...,q-1} be u modulo q.
Use just two fixed group labels, +1 and +2, with graphing domains

    A_1={rho=0},       A_2={rho!=q-1}.

Their total cost is 1/q+(q-1)/q=1. There is one full generator demand, y->Ty.
For rho(y)=r choose the unique indicated path in the integer orbit coordinates
whose phase-zero vertex in this period is called 0:

    r=2k:    2k, 2k-2, ..., 0, 1, 3, ..., 2k+1;
    r=2k+1:  2k+1, 2k-1, ..., 1, 0, 2, ..., 2k+2.

These coordinates are relative to the source's period, not an absolute
measurable choice of orbit origin. Equivalently subtract r from every listed
coordinate and apply the corresponding power of T to y; hence the paths are
measurable functions of rho(y). The odd last residue ends at coordinate q in
the next period. No path uses the forbidden +2 edge starting at residue q-1.
All +1 traversals use the connector from 0 to 1, in either direction.

Every request is covered. The longest path has length q, so each D_n is a
finite routing plan. Its used-edge budget is B(D_n)=1 exactly.

## 3. Exact traffic and entropy

Count requests with sources in one period, using residue classes for edge
starts. The connector traffic and the +2 traffic are

    k_1(r)=q 1_{r=0},
    k_2(2j)=2L-2j-1              (0<=j<=L-1),
    k_2(2j+1)=2(L-1-j)           (0<=j<=L-1).              (4)

For the even +2 edge at 2j, the even source requests with k>j contribute
L-1-j and the odd source requests with k>=j contribute L-j. For the odd +2
edge at 2j+1, the even and odd source requests with k>j each contribute
L-1-j. This proves (4), including the zero value at q-1 and the value one at
q-2. The paths cover all requests, so the graphing indeed generates.

The hidden phase is uniform independently of x. Thus every conditional moment
below is a constant on X:

    p_1=1/q,      m_1=1,
    p_2=1-1/q,    m_2=(L^2+L(L-1))/(2L)=L-1/2.

Since L>=2, clipping at one gives

    J_pi(D_n)=(1-1/q)+(1-(1-1/q))=1.                      (5)

The reuse flags have probabilities

    P(F_1=1 | X)=1/q,      P(F_2=1 | X)=1-2/q.

All flag entropies, with no omitted edge copies, therefore satisfy

    H_pi(D_n)=h(1/q)+h(2/q) -> 0.                         (6)

The joint conditional one-site entropy also tends to zero. In fact the joint
flag probabilities for (1,1),(0,0),(0,1) are respectively 1/q,2/q,1-3/q;
there are no other values. Thus the failure is not an artifact of using a
sum instead of joint entropy.

The tail hypothesis in Section 1 fails decisively. Q_1=q-1 on the connector
and zero otherwise; hence, for each fixed T and all q>T+1,

    Tail_T(D_n) >= (q-1)/q -> 1.                          (7)

The full tail is larger; (7) is the claimed lower bound, not a claim that its
limit is exactly one. Traffic on the +2 edges also grows with q.

## 4. What the countermodel rules out

For one fixed free factor, with a fixed demand and two fixed group labels,
these plans simultaneously have exact optimal source budget, no uncovered
requests, and vanishing integrated conditional entropy of **all** one-site
reuse flags. Nevertheless their conditional defect stays exactly one.
Thus no bound tending to zero can control J merely from these three properties.
The obstruction concerns an attempted entropy-only inference; it invalidates
no currently named Cairn route and does not refute cost preservation.

Indeed this same factor also has a plan with B=1 and J=0: use the full +1
edge, once per demand. Cost preservation asks for suitable plans, and is not
violated by the deliberately bad optimal plans above. Revealing the entire
orbit process of the rare first flag determines rho modulo q, so small
one-site entropy must not be confused with erasing its orbit information.
The useful unresolved task is to choose near-optimal plans that control the
traffic-weighted information error, for example by (1), rather than to infer
that control from one-site entropy alone.

## 5. Evidence and scope

Repository searches on September 12, 2026 checked binary reuse localization,
conditional traffic, finite-fiber descent, and occurrences of odometer and
flag entropy before this construction. The archive already explains the
hypothetical rare-signal/unbounded-traffic mechanism; Sections 2--3 supply an
explicit fixed-factor example with B=1 and J=1. This is a deduction in the
repository's routing formalism, with no priority claim.

The primary-source freshness check was
[Slutsky, Introduction, July 2026](https://arxiv.org/html/2607.20273v1), which
still states the universal Fixed Price problem as open. Definitions and the
aperiodic lower bound used for Z are discussed in
[Gaboriau, What is... cost?](https://arxiv.org/pdf/1011.2294).
These sources are background and status checks, not citations for (1) or (4).

`../binary-descent-entropy-tail-verifier.py` replays the finite paths and their
traffic counts with exact integer and rational arithmetic for specified
powers of two. The all-n proof is the counting argument above; a finite replay
alone is not a universal proof or verification of infinite-action cost theory.
