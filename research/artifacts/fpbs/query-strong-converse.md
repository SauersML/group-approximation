# Connection certificates below the information budget

The objective is the full every-Cayley-graph Benjamini--Schramm theorem.
This note sharpens the necessary search estimate in
`exploration-information.md` from an expectation bound to an exponential
probability bound. It also weakens the sufficient algorithmic task: one
would only need a sufficiently cheap search with subexponential success
probability under hypothetical collapse. That construction is NOT proved
here, and the universal goal remains OPEN.

## 1. A bounded adaptive experiment is dominated by a binomial experiment

Fix 0<c<q<1. A search uses a parameter-independent random seed and
adaptively queries distinct edges of an infinite graph. Its decisions
use only that seed, graph geometry and observed answers. Let E_m be
the event that it has produced a checked open path between its specified
endpoints using at most m fresh queries. The endpoints may be part of
the independent seed. No termination or expected-cost hypothesis is
needed for the uncapped search.

Cap the search after m fresh queries. If it stops earlier, pad the
experiment to m by querying unused edges in a fixed enumeration. The
success event remains measurable, and conditional on the seed the m
answers are independent Bernoulli(p). Adaptivity changes their edge
names but not their conditional distributions. With U the number of
open answers, the likelihood ratio of the padded transcript is

    L_m = (q/c)^U * ((1-q)/(1-c))^(m-U).                   (1)

For alpha>1, define

    D_alpha(q||c) = log(q^alpha*c^(1-alpha)
                     +(1-q)^alpha*(1-c)^(1-alpha))
                   /(alpha-1).

**Proposition 1.** If P_c(E_m)<=a, then

    P_q(E_m) <= a^((alpha-1)/alpha)
                * exp(m*(alpha-1)*D_alpha(q||c)/alpha).  (2)

There is also an exact bound P_q(E_m)<=B_m(a). Let H_p be a binomial
random variable with parameters m,p. Choose t in {0,...,m} such that

    P(H_c>t) <= a <= P(H_c>=t).

Then

    B_m(a) = P(H_q>t)
             + [a-P(H_c>t)]*P(H_q=t)/P(H_c=t).            (3)

At a=0 or 1 this gives 0 or 1. The bound is optimal over all events
of c-probability at most a in the padded experiment, with independent
randomization permitted at its threshold. It need not be attainable
by a path certificate.

**Proof.** Holder's inequality gives
E_c[L_m 1_{E_m}] <= P_c(E_m)^((alpha-1)/alpha)
*(E_c L_m^alpha)^(1/alpha). The last moment is the m-th power of
the one-answer moment in the definition of D_alpha, proving (2).
For (3), L_m is strictly increasing in U. The event of largest q-mass
at fixed c-mass therefore takes U>t and the required fraction at U=t.
More explicitly, subtract its randomized indicator f from any admissible
indicator g. Pointwise, (L_m-L_m(t))*(g-f)<=0, while
E_c(g-f)<=0. It follows that E_c L_m(g-f)<=0. Its q-mass is exactly
(3). The seed is independent and contributes no likelihood factor; it
can supply the boundary randomization. QED.

For alpha=2, (2) becomes the particularly simple inequality

    P_q(E_m)^2 <= a * [1+(q-c)^2/(c*(1-c))]^m.             (4)

Finite tests below also check the unpadded stopped-prefix martingale
E_c[L_N^2/A^N]=1, for N<=m and A=1+(q-c)^2/(c*(1-c)).
One must not replace the padded moment by A^(E N), or assume
E_c L_N^2=E_c A^N: the stopping time depends on the answers.

## 2. Critical spectral decay gives a strong converse

Fix a nonamenable d-regular Cayley graph, c=p_c, and an independent
lazy walk (X_n) started at o. Let rho<1 be the walk's operator norm
and lambda=-log rho. The existing critical correlation theorem states

    P_c(o connected to X_n) <= exp(-lambda*n).

The seed can include the entire walk. Any finite path certificate
between o and X_n implies actual connectivity, so Proposition 1 yields

    P_q(certificate by m queries)
      <= exp[-(alpha-1)/alpha
                    * (lambda*n-m*D_alpha(q||c))].        (5)

Write k(q,c)=q log(q/c)+(1-q) log((1-q)/(1-c)). Differentiating
the finite expression defining D_alpha, or applying l'Hopital's rule,
gives D_alpha(q||c)->k(q,c) as alpha decreases to 1.

**Theorem 2.** For every b<lambda/k(q,c), there is eta>0 such that
any family of these algorithms satisfies

    P_q(certificate by floor(b*n) queries) <= exp(-eta*n) (6)

for all n>=1. This allows a different algorithm for each n; each must
use the same rule under parameters c and q.

**Proof.** Choose alpha>1 close enough to 1 that
b D_alpha(q||c)<lambda, and set
eta=(alpha-1)/alpha*(lambda-b D_alpha(q||c)). Apply (5) and
floor(b*n)<=b*n. QED.

For a uniqueness parameter q>c let I_n be the event that both endpoints
lie in infinite clusters. Positive association and transitivity give
P_q(I_n)>=theta(q)^2>0. Consequently

    P_q(certificate by floor(b*n) queries | I_n)
      <= theta(q)^(-2)*exp(-eta*n).                       (7)

In particular this lower cost is not attributable solely to rare searches
with a very large query count. Conditional on I_n, the fraction of
searches completing below b*n tends to zero exponentially.

There is also an almost sure conclusion on any common probability space
carrying the percolation, walk and the algorithm seeds for all n. By
Borel--Cantelli, only finitely many n admit such a cheap certificate,
almost surely. No independence between different n is required. Taking
a countable sequence b increasing to lambda/k gives

    liminf_{n->infinity} T_n/n >= lambda/k(q,c) a.s.,      (8)

where T_n is the number of queries needed to produce a path, and is
infinity when the algorithm never produces one. In a uniqueness phase,
an exhaustive connection search has T_n<infinity on I_n, so (8) also
holds along those indices. No assertion that I_n occurs infinitely
often is required for this statement. Unlike the earlier mean-bound
argument, no finite-cluster susceptibility or finite-cost hypothesis
is used.

For clarity, (8) is an assertion for each fixed q and a prescribed
countable algorithm family. It does not assert a simultaneous result
for every uncountable choice of parameter or algorithm after seeing
the percolation.

## 3. The sharp quadratic scale of this bound

Put v=c(1-c), epsilon=q-c. For each fixed alpha>1, Taylor expansion
of the explicit two-term expression gives

    D_alpha(c+epsilon||c)
       = alpha*epsilon^2/(2v)+O(epsilon^3).                (9)

Fix 0<B<2v lambda and consider the query cap floor(B*n/epsilon^2).
Take alpha=sqrt(2v lambda/B)>1. The exponent per walk step in (5)
then converges, as epsilon decreases to zero, to

    (sqrt(lambda)-sqrt(B/(2v)))^2 > 0.                   (10)

Thus below the earlier constant 2c(1-c)lambda, cheap successful
searches are exponentially unlikely, with a positive limiting
unconditional exponent. Conditional on I_n, (7) still has the factor
theta(q)^(-2). We do not claim uniform conditional convergence in a
joint limit without accounting for that factor.

## 4. What a walk tube can and cannot achieve

Let V_R=|B_G(o,R)| and let H_{n,R} be the subgraph induced by
the union of B_G(X_i,R), i=0,...,n. It has at most

    m_{n,R} <= d*(n+1)*V_R/2

edges. Reading all these edges and testing connection in this finite
subgraph is a valid certificate algorithm; the tube depends only on
the independent walk. Write b_R=d V_R/2. If

    b_R < lambda/k(q,c),                                 (11)

then for some eta>0 and finite K depending on q,R,

    P_q(o connected to X_n inside H_{n,R}) <= K e^(-eta*n).

Indeed, choose alpha as in Theorem 2 and apply (5) with
m<=b_R(n+1). The additive b_R contributes only the constant
K=exp((alpha-1)b_R D_alpha/alpha). The same conclusion conditional
on I_n has the additional factor theta(q)^(-2).

It follows that a fixed width R whose tube connection probability
decays only subexponentially must satisfy

    V_R >= 2lambda/(d k(q,c)).                            (12)

For d>=3, the elementary nonbacktracking path count gives
V_R<=d(d-1)^R/(d-2). Hence (12) implies

    R >= log(2lambda*(d-2)/(d^2*k(q,c)))/log(d-1).

If such radii R(q) existed along uniqueness parameters decreasing to c,
they would therefore obey

    R(q) >= 2 log(1/(q-c))/log(d-1)+O_G(1).               (13)

This is a necessary width bound. Uniqueness does not, in this argument,
give a fixed width with subexponential tube connection probability at
any q<1. Enlarging the tube to capture a connection at each fixed n
does not justify interchanging the n and R limits.

## 5. The construction that would finish this approach

Under hypothetical threshold collapse, it would suffice to construct,
for some q>c and b<lambda/k(q,c), algorithms with at most floor(b*n)
queries whose probabilities of producing a path between o and X_n
have exponential rate zero along an unbounded subsequence of n.
For example, probabilities exp(-o(n)) would contradict (6).
The construction need not finish an exact connectivity decision or
have an integrable unbounded stopping time. This removes those burdens
from the earlier sufficient search target.

No such construction is supplied. In particular neither global
uniqueness nor the existence of a finite connecting path yields the
required query budget. Section 4 rules out the simplest fixed-width
shortcut when its volume is below that budget. To complete the universal
theorem, one still needs a probabilistic mechanism that supplies these
cheap certificates under collapse, or a different argument excluding
collapse. These estimates do not prove the requested open interval.

The available published geometry results checked for this step do not
close it. Hermon--Hutchcroft's fixed-supercritical finite-cluster tails
and anchored expansion are [Theorem 1.1 and Corollary 1.4](https://arxiv.org/pdf/1904.10448).
They do not provide the required query construction. Hutchcroft's
quantitative near-critical volume and radius estimates in
[Theorems 1.1 and 1.2](https://arxiv.org/pdf/2002.02916) assume
p_c<p_{2->2}; that hypothesis is precisely an unresolved sufficient
condition in the universal task. Using those estimates unconditionally
would reintroduce the missing premise. This is a check of these specific
inputs, not an assertion that every possible geometric method fails.

## 6. Verification scope

`scripts/replay_query_strong_converse.py` enumerates finite graph
configurations using the shared exploration engine. At every query cap
it checks exact prefix cylinder probabilities, likelihood ratios, the
normalized stopped second-moment identity, (4), and the exact binomial
bound (3), all with rational arithmetic. Its report is
`query-strong-converse-replay.json`. These tests check the finite
experiment calculations; the infinite claims rely on the written
proofs and Cairn's existing critical-correlation input. Cairn dependency
validation is not formal proof verification.

The MSI replay passed 558 cap cases, using 1,548 graph configurations
and 2,776 stopped prefixes, in about 0.8 seconds.
