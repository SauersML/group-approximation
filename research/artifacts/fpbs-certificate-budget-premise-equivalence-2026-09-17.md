# The certificate-budget premise is the Benjamini--Schramm conjecture

Worker b-t-optcert, wave swarm-0917, role inverter, 2026-09-17.
Target hole: `fpbs-universal-optimistic-certificate-budget`.
Goal: `fpbs-benjamini-schramm-universal`.

## 0. Summary

The query strong converse `fpbs-bounded-query-connection-strong-converse`
is **unconditional**. It holds on every nonamenable Cayley graph, at every
q in (p_c,1), for every admissible bounded search. The conclusion of the
budget premise is therefore false on every graph, at every parameter, for
every algorithm. The premise is an implication "collapse implies that
conclusion", so it is true exactly when collapse is false. For each graph
the premise is equivalent to p_c<p_u, and the universal premise is
equivalent to the universal goal.

Consequences:

1. The route `fpbs-universal-optimistic-certificate-route` restates the
   goal; it is not a decomposition. Its bounty (2) consists of the goal
   itself.
2. No choice of algorithm carries information. For every admissible search
   family A, the premise P_A obtained by substituting A for the optimistic
   search is equivalent to p_c<p_u. Different selectors, relaxed path
   objectives, tie rules, planning caps, walk tubes and waypoint schemes all
   give the same premise up to logical equivalence.
3. **Class kill.** Consider any two-step derivation collapse => Psi =>
   cheap certificates. Its second leg is valid only if Psi holds at no
   admissible triple (graph, parameter, algorithm). Every intermediate
   property that is realized at some existing supercritical parameter of
   some nonamenable Cayley graph dies at the second leg. There it
   contradicts the converse exponent eta=(alpha-1)(lambda-b D_alpha)/alpha>0.
4. The same equivalence covers the natural weakenings of the premise:
   success along a subsequence, success conditional on both endpoints
   lying in infinite clusters, and expected cost below budget for a search
   that always succeeds on that event.

Nothing here decides the goal. The result moves the mathematical content
of the certificate program. That content lies entirely in extracting,
from collapse, a property of Bernoulli percolation that fails at every
supercritical parameter of every nonamenable Cayley graph. The search
machinery can add nothing on top of such a property.

## 1. Setting and admissibility

G = Cay(Gamma,S), with Gamma finitely generated and nonamenable and S a
finite symmetric generating set. Put c=p_c(G). Put rho for the lazy-walk
operator norm, which is <1 by Kesten, and lambda=-log rho>0. Nonamenability
gives 0<c<1. X_n is the independent lazy-walk endpoint and
k(q,c)=q log(q/c)+(1-q) log((1-q)/(1-c)).

A search family A=(A_n) is **admissible with budget b** if:

- each A_n uses a seed independent of the percolation, which may include the
  walk;
- its rule is the same under every parameter;
- it queries distinct edges adaptively and stops after at most floor(b n)
  fresh queries;
- when it returns a path, every edge of that path has been queried open.

The optimistic search with query cap floor(b n) and deterministic planning
cap M_n is admissible. Its seed is the walk and its rule is fixed. By
`fpbs-optimistic-search-certified-growth` a returned path is a path of
queried-open edges. Censoring by either cap makes the run bounded.

For such A put r_A(G,q,b) = limsup_n n^(-1) log P_q(A_n returns a path),
with log 0=-infinity.

**Imported theorem (established node
`fpbs-bounded-query-connection-strong-converse`, Theorem 2 of
`research/artifacts/fpbs/query-strong-converse.md`).** Verbatim from
the node: "For 0<c<q<1 and alpha>1, the probability that an adaptive
algorithm certifies o connected to X_n in at most m fresh queries is at
most exp(-(alpha-1)(lambda*n-m*D_alpha(q||c))/alpha). The seed is
independent of percolation and the rule is the same under c and q. Thus
any linear budget b<lambda/k(q,c) gives exponential decay."

The theorem has no collapse hypothesis. It uses only the critical walk
correlation `fpbs-critical-walk-correlation`, P_c(o<->X_n)<=rho^n, and
this bound holds on every nonamenable Cayley graph.

## 2. Unconditional failure of cheap certificates

**Lemma 1.** For every G as above, every q in (c,1), every b with
0<b<lambda/k(q,c) and every admissible A with budget b:

    r_A(G,q,b) <= -eta < 0,  eta=(alpha-1)(lambda-b D_alpha(q||c))/alpha,

for any alpha>1 with b D_alpha(q||c)<lambda. Such an alpha exists because
D_alpha(q||c) decreases to k(q,c) as alpha decreases to 1.

*Proof.* The event "A_n returns a path" is contained in the event "A_n
certifies o<->X_n with at most floor(b n)<=b n fresh queries". Apply the
imported bound with m=floor(b n) and use the monotonicity of the exponent
in m. QED.

## 3. Equivalence

For an admissible rule A (a way of assigning an admissible family to each
q, b and cap choice), write P_A(G) for the statement:

> If p_c(G)=p_u(G), then there exist q in (c,1), b in (0,lambda/k(q,c))
> and caps such that r_A(G,q,b)=0.

The hole `fpbs-universal-optimistic-certificate-budget` is the conjunction
of P_opt(G) over all G, with A=opt the optimistic search.

**Theorem 2.** For every G and every admissible rule A,

    P_A(G)  <=>  p_c(G) < p_u(G).

Consequently

    fpbs-universal-optimistic-certificate-budget
       <=> fpbs-benjamini-schramm-universal.

*Proof.* The implication (<=) is vacuous: the hypothesis of P_A(G) is
false. For (=>), suppose P_A(G) holds and p_c(G)=p_u(G). Then P_A(G)
supplies q,b and caps with r_A=0, while Lemma 1 gives r_A<=-eta<0. This is
a contradiction. Hence p_c(G)!=p_u(G), and p_c<=p_u gives p_c<p_u.

For the universal statements: both quantify over all locally finite Cayley
graphs of nonamenable groups. The goal excludes the identity from S. A loop
edge never changes any cluster, so p_c and p_u are unchanged by adding or
removing loops. The two quantifier ranges therefore give the same threshold
statements. QED.

**Corollary 3 (algorithm independence).** For any two admissible rules A,
A' and every G, P_A(G) <=> P_{A'}(G). No refinement of the search (a
different selector, a relaxed path objective, a different tie rule or cap,
exhaustive reading of a walk tube, waypoint concatenation) produces a
premise that is weaker or stronger than another.

## 4. Weakened conclusions are equally equivalent

Each of the following conclusions is false for all (G,q,b,A) with b below
the budget. Substituting any of them into the premise gives again a
statement equivalent to p_c(G)<p_u(G).

(a) *Subsequence.* P_q(A_n returns a path)>=exp(-o(n)) along an unbounded
subsequence. Lemma 1 bounds every n.

(b) *Conditioning on infinite endpoints.* Let I_n be the event that both
o and X_n lie in infinite clusters. If P_q(success | I_n)>=exp(-o(n)),
then P_q(success)>=theta(q)^2 exp(-o(n)). By Harris--FKG and transitivity
P_q(I_n)>=theta(q)^2. Under collapse theta(q)>0 for q>c, so r_A=0,
contradicting Lemma 1. (This is the established conditional form in
`fpbs-uniqueness-query-quantiles-and-tube-width`.)

(c) *Expected cost on I_n.* Take an uncapped search that returns a path on
every configuration in which o and X_n are connected, and suppose
E_q[N_n | I_n]<=b n with b<lambda/k(q,c). Under collapse, uniqueness at q
means I_n is contained in {o<->X_n} almost surely. Pick b' in
(b,lambda/k(q,c)). By Markov's inequality, cap at floor(b' n). The capped
search is admissible with budget b', and it succeeds with probability at
least theta(q)^2 (1-b/b'). This contradicts Lemma 1 at budget b'. The
uncapped optimistic search qualifies by the terminating clause of
`fpbs-optimistic-search-certified-growth`.

## 5. Class kill: no satisfiable intermediate property

Let Psi be any property of triples T=(G,q,A), where G is a nonamenable
Cayley graph, q is in (p_c(G),1) and A is admissible with some budget
b<lambda(G)/k(q,p_c(G)).

**Theorem 4.** Suppose the implication "Psi(T) => r_A(G,q,b)=0" is valid
for all such T. Then Psi(T) holds for no T.

*Proof.* A triple with Psi(T) would satisfy r_A=0, contradicting Lemma 1.
QED.

**Where every member dies.** A derivation of the hole has the form
collapse(G) => Psi(G,q,A) => r_A=0. Its second leg can be valid only for
an unsatisfiable Psi. The class of derivations whose Psi is realized at some
existing triple is therefore dead at the second leg in every member. At the
realizing triple the claimed success rate 0 contradicts the explicit
exponent eta>0 of Lemma 1. The invariant separating these derivations is
the converse exponent eta(q,b)=(alpha-1)(lambda-b D_alpha)/alpha. It is
positive at every admissible triple and blind to whether collapse holds.

Members killed include every argument whose intermediate step is any of the
following, whenever that step is realized at some supercritical parameter
of some nonamenable Cayley graph:

- uniqueness at q;
- fixed-supercritical finite-cluster tails or anchored expansion of the
  infinite cluster (the Hermon--Hutchcroft inputs already checked in
  `query-strong-converse.md` Section 5; those notes found they "do not
  provide" the construction, and Theorem 4 shows no such input *can*);
- positive theta(q) together with linear chemical distance;
- volume or width bounds for walk tubes;
- finite pilots or finite verifications, which realize only finite data.

The following remark is not load-bearing and is not imported. Nonamenable
Cayley graphs with p_c<p_u<1 are expected to supply realizations, for
example planar hyperbolic surface-group graphs. The theorem itself is
stated for realized properties and needs no such example.

## 6. What survives, and where to spend effort

Any valid derivation must pass through a property that no nonamenable
Cayley graph has at any supercritical parameter. Such a property holds
only in a collapsed world. The certificate machinery then adds nothing: the
first leg, collapse => Psi, already is a proof of the goal for G, because
Psi is refutable directly.

The productive targets are therefore collapse-specific properties that
are directly contradictory, such as:

- the exponential pivotal spikes of `fpbs-collapse-exponential-pivotal-spikes`,
  which are paired with an upper growth estimate;
- p_{2->2}=p_c, which follows from collapse because p_c<=p_{2->2}<=p_u, paired
  with operator estimates;
- the scale-crossover exponents of `fpbs-uniqueness-scale-crossover`.

None of these goes through query algorithms. Section 2 of
`research/artifacts/fpbs/optimistic-search.md` suggests that "a proof may
need a different selector or a relaxed path objective". By Corollary 3
that suggestion changes nothing.

## 7. Verification scope

Sections 2--5 are short logical consequences of the established strong
converse and certified-growth nodes. They use no new estimates, and
nothing is computed. A referee should check two things:

1. The imported converse has no collapse or uniqueness hypothesis. The node
   text and Section 2 of `query-strong-converse.md` state it for 0<c<q<1
   on every nonamenable Cayley graph, with c=p_c.
2. The optimistic search with finite caps satisfies the admissibility
   conditions of that theorem. `fpbs-universal-optimistic-certificate-route`
   itself asserts this: "finite planning and query caps make it a bounded
   experiment with no unqueried percolation information in its seed".
