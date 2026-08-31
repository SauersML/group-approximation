---
rg: 2
id: bcv-perfect-answer-reduction-decodes-double-cover
kind: claim
title: Every attained-perfect BCV Answer Reduction strategy exactly decodes the source double cover
distinct_from:
  bcv-honest-answer-reduction-retains-readable-closure: that follows only BCV's chosen forward completeness strategy; this decodes every attained perfect target strategy backward.
  jnvwy-perfect-answer-reduction-exactly-reflects-source-atoms: that proves the analogous zero-loss rigidity for the JNVWY verifier; this uses BCV Definition 5.79 and its ALine, DLine, indifference, and oracle-PCP checks.
  bcv-question-reduction-retains-readable-closure: that treats the Pauli packet in Question Reduction; this treats the subsequent Answer Reduction and does not by itself assert universal Pauli-block amplification.
---

**ESTABLISHED (attained value one).** Fix the Answer Reduced game of
Bowen--Chapman--Vidick, Definition 5.79, with individual-degree parameter
`d=9), `m>=1), and `q>63m). Let `S` be an attained perfect
strategy in a faithful finite tracial measurement algebra `(M,tau)`;
this includes the faithful quotient of a finite-dimensional synchronous
strategy. Then, without changing `M), `S` has an exact decoding

```text
Dec(S): perfect Oracle(DoubleCover(V_n))
          -> perfect DoubleCover(V_n).                  (BAD1)
```

In matrices the decoded strategy has the same dimension. If `S` is a
signed-permutation ZPC strategy, `Dec(S)` can be chosen ZPC, with the
readable/unreadable types preserved literally, and

```text
D_infinity(Dec(S)) subseteq D_infinity(S).               (BAD2)
```

Thus finite or bounded readable closure passes backward through Answer
Reduction. The `q^(-1)` term in Proposition 5.80 and Theorem 5.1 is a
robust positive-error floor; it is not an obstruction at attained error
zero.

The universal conclusion in `(BAD1)` is the double cover, not the
uncovered source. It gives a perfect strategy for `V_n` under either of
the following exact hypotheses:

1. every source question has a positive-weight synchronization loop, by
   Claim 3.54 at error zero; or
2. the nontrivial source question graph is bipartite, by Remark 3.55,
   choosing one double-cover sheet on each side.

The second case is the one used by the actual Question-Reduction-to-Answer-
Reduction pipeline. Theorem 4.36 outputs
`DeType(QueRed(...))`; Definition 4.40 puts genuine A-questions and
B-questions in disjoint copies, while their only common zero anchor has
answer length zero and autoaccepts. Hence the decoded double-cover strategy
restricts exactly to that source game. Subsequent inverse purification and
padding are value-preserving restriction operations (Fact 5.41 and Fact
4.48).

This scope is sharp. Without synchronization or bipartiteness, take the
loopless triangle game with one bit per question and the constraint that
adjacent bits differ. Perfectness would force binary observables
`U_1=-U_0`, `U_2=-U_1`, and `U_0=-U_2`, a contradiction. Its double
cover is the six-cycle and has a deterministic perfect coloring. The
perfect-completeness construction in Proposition 5.80, equations
`(192)--(193)`, starts from the perfect oracularized double-cover model
and therefore gives a perfect Answer Reduced model. So no unconditional
exact inverse from Answer Reduction all the way to `V_n` is possible.

The assertion concerns an actual perfect model. If value one is only a
nonattained supremum of finite-dimensional strategies, a tracial
ultraproduct gives and decodes a perfect limit model, but this alone does
not produce a finite-dimensional attained source strategy.
