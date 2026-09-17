---
rg: 2
id: fpbs-critical-l2-equivalent-to-dyadic-projection-estimate
kind: claim
title: The dyadic projection estimate is equivalent to critical l2 boundedness and then has exponent three halves
distinct_from:
  fpbs-dyadic-projections-bound-connectivity: that is the easy direction, summable dyadic projection norms bound the critical connectivity operator; this is the converse, a bounded critical operator forces the dyadic norms to decay like 2^(-3k/2), which makes the two conditions equivalent.
  fpbs-critical-dyadic-projection-estimate: that is the universal OPEN hole Q2 on every nonamenable Cayley graph; this proves Q2 exactly on the graphs where the critical connectivity operator is bounded, and nowhere else, without deciding when that happens.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that is Hutchcroft's l2 conjecture; this shows Q2 and Q3 are each equivalent to it graph by graph.
  fpbs-regular-tree-dyadic-three-halves: that computes the shell norms exactly on regular trees; this gives the same N^(-3/2) upper bound on every transitive graph with a bounded critical operator, by a ghost-field tree-graph bound with no branching structure.
  fpbs-projection-resolvent-ghost-obstruction: that shows a ghost-killed resolvent bound cannot be subtracted to bound connectivity; this uses the ghost field differently, as a BK witness for large clusters, and assumes the connectivity bound instead of trying to derive it.
---

Let `G=(V,E)` be a connected, locally finite, transitive graph, `p=p_c(G)`,
`tau(x,y)=P_{p_c}(x<->y)` and `T` the operator with kernel `tau`. For `n>=1`
put `T^(>=n)(x,y)=P_{p_c}(x<->y, |K_x|>=n)`; let `Q_k` be the shell
projections of Section 2.2 of `research/artifacts/fpbs/creative-branches.md`,
`Q_k(x,y)=E[1{x<->y, 2^k<=|K_x|<2^(k+1)}/|K_x|]`, and
`M_h=E_{p_c}[1-exp(-h|K_o|)]` the critical magnetization.

**Theorem.**

1. *(Unconditional, entrywise.)* For every `n>=1` and all `x,y`,
   `T^(>=n)(x,y) <= (e/(e-1)) M_(1/n) (T^2)(x,y)`, where
   `(T^2)(x,y)=sum_z tau(x,z)tau(z,y)` may be infinite.
2. *(Conditional norm bound.)* If `||T||_(2->2)<infinity` there is
   `C<infinity` with, for all `n>=1` and `k>=0`,

       ||T^(>=n)||_(2->2) <= (e/(e-1)) M_(1/n) ||T||^2 <= C ||T||^2 n^(-1/2),
       ||Q_k||_(2->2) <= 2^(-k) ||T^(>=2^k)|| <= C ||T||^2 2^(-3k/2).

   So Q3 holds with `eta=1/2` and `sum_k 2^k ||Q_k|| <= 4C||T||^2 < infinity`
   (Q2). Without the imported magnetization bound, the same argument gives
   `sum_k 2^k||Q_k|| <= (e/(e-1)) ||T||^2 (E log_2(1+|K_o|) + 3)`.
3. *(Equivalence.)* On every such graph whose critical clusters are a.s.
   finite (in particular every nonamenable Cayley graph, the setting of Q2),
   the following are equivalent:
   (Q2) `sum_k 2^k||Q_k||<infinity`; (Q3) `||Q_k||<=C 2^(-3k/2)`;
   (L2) `||T_{p_c}||_(2->2)<infinity`.
4. *(Sharpness.)* The exponent `3/2` cannot be improved in the tail sense:
   `sum_(j>=k) 2^j ||Q_j|| >= P(|K_o|>=2^k)/2 >= c 2^(-k/2)` on every
   transitive graph with finite critical clusters, by the diagonal entry and
   the universal Aizenman-Barsky lower bound.

Consequences. The universal hole `fpbs-critical-dyadic-projection-estimate`
is, graph by graph, the same statement as Hutchcroft's l2 conjecture
`fpbs-nonamenability-bounds-critical-connectivity-operator`, and its
"strictly stronger" variant Q3 is not stronger. Q2 and Q3 with `eta=1/2` hold
on every Cayley graph in the known critical-l2 classes (Gromov hyperbolic,
nonunimodular, acylindrically hyperbolic, free products on union generating
sets), because `p_c<p_(2->2)` gives `||T_{p_c}||<=||T_p||<infinity` for some
`p>p_c` by entrywise monotonicity.
