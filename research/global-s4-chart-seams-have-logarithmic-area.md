---
rg: 2
id: global-s4-chart-seams-have-logarithmic-area
kind: claim
title: Globally named conjugate S4 charts have seam area at least logarithmic in the leaf count
distinct_from:
  finite-mark-centralizer-commutator-area-is-proper: that is the general area lower bound for commutators of one fixed finite-order word with centralizer elements; this applies it to the S4-chart complex of Thompson's V and adds the Johnson-graph counting that turns it into a depth lower bound.
  thompson-v-r5-uniform-common-pivot-centralizers: that refuted one explicit family of common-pivot centralizer bounds; this refutes every global assignment of conjugate S4 charts on the leaf complex, whatever conjugating words are chosen.
  thompson-v-r5-coherent-alternating-packet: that is the open all-pairs compiler; this kills only its literal word-level S4-chart formulation.
---

**ESTABLISHED.** Fix the Bleak--Quick presentation `V=<X|R>`, four depth-three
cylinders `c_1,...,c_4`, and fixed words `tau_ab` for the swaps `(c_a c_b)`.
For `N=2^n`, choose for every four-subset `S={p_1,...,p_4}` of depth-`n`
leaves a word `gamma_S` for an element `g_S` with

```text
g_S (c_a c_b) g_S^(-1) = (p_a p_b)            (1<=a<b<=4),
```

and name the chart edges `w_S(p_a p_b)=gamma_S tau_ab gamma_S^(-1)`. Then
there are `c>0` and `c'`, depending only on the presentation and the fixed
words, such that for every `n` and every choice of the `gamma_S`,

```text
max Area_R( w_S(pq) w_(S')(pq)^(-1) ) >= c n - c',       (GSC)
```

the maximum over adjacent `S,S'` (`|S intersect S'|=3`) and shared edges
`{p,q}`. So no global choice makes every shared-edge comparison in a five-set
a bounded-use consequence of R1--R5, let alone of R2, R4 and R5 alone: the
S4-chart audit of `thompson-v-r5-coherent-alternating-packet` has a negative
answer at the word level.

The same counting works for conjugate charts on `k`-subsets for every fixed
`k>=3`, since adjacent charts share an edge and `J(N,k)` has diameter `k`.
This includes charts named per five-set whose cross-context comparisons are
all bounded.

**Averaged form.** Averaging does not help at the word level. For suitable
`c>0` and `c'`, more than one eighth of all adjacent pairs `S,S'` have every
shared-edge comparison of area at least `c n - c'`. So word-level averaged
synchronization fails as well, and only matrix estimates that are not area
bounds remain undecided.
