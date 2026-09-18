---
rg: 2
id: fpbs-certificate-budget-premise-is-equivalent-to-goal
kind: claim
title: The optimistic certificate-budget premise is equivalent to the Benjamini--Schramm goal, for every search algorithm
distinct_from:
  fpbs-universal-optimistic-certificate-budget: that is the open premise; this proves it equivalent to threshold separation graph by graph, so it stays open exactly as long as the goal does and its route is a restatement, not a decomposition.
  fpbs-bounded-query-connection-strong-converse: that bounds certificate probabilities below the information budget; this observes that the bound has no collapse hypothesis, so every cheap-certificate premise is equivalent to p_c<p_u, and kills every intermediate property realized at an existing supercritical parameter.
  fpbs-uniqueness-query-quantiles-and-tube-width: that derives necessary cost and tube-width constraints under uniqueness; this shows that every algorithmic premise meant to meet those constraints is logically the goal itself.
artifacts:
  - research/artifacts/fpbs-certificate-budget-premise-equivalence-2026-09-17.md
---

Let G be a locally finite Cayley graph of a nonamenable group. Put c=p_c(G)
and lambda=-log rho. Call a search family admissible with budget b if:

- its seed is independent of the percolation;
- its rule does not depend on the parameter;
- it stops after at most floor(b n) fresh queries;
- it returns only paths of queried-open edges.

Examples are the capped optimistic search, any other selector or relaxed
path objective, and exhaustive reading of a walk tube.

**(a)** For every admissible family A, every q in (c,1) and every
b<lambda/k(q,c), the success rate limsup n^(-1) log P_q(A returns a path
from o to X_n) is at most -eta<0. The conclusion of
`fpbs-universal-optimistic-certificate-budget` is therefore false on every
graph, at every parameter, for every algorithm, whether or not the
thresholds collapse.

**(b) Equivalence.** For every G and every admissible A, the premise "if
p_c(G)=p_u(G) then A has success rate 0 for some q in (c,1) and
b<lambda/k(q,c)" holds if and only if p_c(G)<p_u(G). Hence
`fpbs-universal-optimistic-certificate-budget` is equivalent to
`fpbs-benjamini-schramm-universal`.

Substituting any other admissible algorithm gives an equivalent premise. So
does any of these weakened conclusions:

- success along a subsequence;
- success conditional on both endpoint clusters being infinite;
- expected cost below budget for a search that always succeeds on connected
  pairs.

**(c) Class kill.** Suppose an implication Psi(G,q,A) => success rate 0
is valid. Then Psi holds at no admissible triple. Consider any derivation
collapse => Psi => cheap certificates whose intermediate Psi is realized at
some existing supercritical parameter of some nonamenable Cayley graph,
such as:

- uniqueness at q;
- fixed-supercritical finite-cluster tails or anchored expansion;
- linear chemical distance;
- tube volume bounds;
- finite pilots.

Every such derivation dies at the leg Psi => cheap certificates. There it
contradicts the explicit converse exponent
eta=(alpha-1)(lambda-b D_alpha(q||c))/alpha>0, an invariant that does not
see collapse.

What survives: any valid proof must extract from collapse a property that
no nonamenable Cayley graph has at any supercritical parameter. The query
machinery cannot add content beyond that first leg.
