---
rg: 2
id: fpbs-nonamenability-bounds-critical-connectivity-operator
kind: claim
title: Nonamenability makes the critical connectivity operator bounded on l2
root: true
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/creative-branches.md
  - research/artifacts/fpbs/exploration.md
---

**OPEN.** For every connected, locally finite, nonamenable transitive graph
`G=(V,E)`, the matrix of critical connection probabilities

```text
T_{p_c}(u,v) = P_{p_c}(u <-> v)
```

is bounded as an operator `l2(V) -> l2(V)`. This is Hutchcroft's L2
boundedness conjecture, stated in arXiv:1904.05804. Only finiteness is asked
for; the bound may depend on the graph.

It implies `fpbs-benjamini-schramm-universal` through
`fpbs-critical-l2-implies-nonuniqueness`, and also implies mean-field critical
behaviour, so it is a **strictly stronger conjecture** than the percolation
goal, not a consequence of nonamenability that anyone has proved. Section 2 of
`research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md` warns
explicitly against mistaking a clean sufficient condition for a solved
difficult part; that warning is the reason this node is OPEN and separate from
the imported implication.

The forwarded 2026-09-09 priority verdict nonetheless identifies this as the
concrete finishing theorem that makes Benjamini--Schramm the primary
affirmative target: the desired conclusion needs only a finite bound with a
graph-dependent constant, so rough but structurally correct estimates are
admissible, and neither threshold, critical exponent nor universal numerical
gap has to be computed.

## Attempts

* **Dyadic decomposition of the critical clusters** (response 4,
  `creative-branches.md` Section 2.2; response 8, `exploration.md` Sections
  3--4). Write `<f,T_{p_c} f> <= sum_k 2^(k+1) <f,Q_k f>` where `Q_k` averages
  over clusters of size in `[2^k,2^(k+1))`, so the size-weighted summability
  `fpbs-critical-dyadic-projection-estimate` would give boundedness. On every
  regular tree the estimate holds sharply, `||Q_N|| asymp N^(-3/2)`, with an
  exact closed formula. **Where it dies:** Theorem 6 of `exploration.md`
  constructs a group-equivariant factor of iid on the nonamenable graph
  `T_4 x Z` with all clusters finite, `E|C_o|=infinity`, and divergent dyadic
  sum. Nonamenability, finiteness of clusters and FIID admissibility therefore
  do not imply the estimate; the heavy-tailed intervals keep an amenable
  direction in which the shell projections have large operator norm. Any proof
  must use that all edges incident to a vertex share one independent retention
  law, or something equally restrictive.
* **Bound a single root overlap and iterate.** Composing two independent
  cluster projections gives the exact identity
  `<delta_o, Q_k^2 delta_o> = E[1{both in shell k} |C intersect C'|/(|C||C'|)]`
  (`creative-branches.md` Section 2.3), suggesting control of chains of
  intersections by expansion plus the rank-one merger cancellation (Q1).
  **Where it dies:** the same section states the obstruction. A root-overlap
  bound controls a trace moment, not an operator norm; rare or highly aligned
  spectral directions still matter, and no argument here controls arbitrary
  test functions or high enough spectral moments.
* **Reformulate as ghost regularity.** Weighting the cluster averages by
  `e^(-t|C|)` makes `||Q(0)-Q(t)|| <= Mt` *equivalent* to boundedness of
  `T_{p_c}` (`creative-branches.md` Section 2.4). **Dead as progress:** the
  note records that this is an equivalence, hence a restatement of the
  conjecture in positive-operator language, not a weaker solved substitute.
* **Read it off the established special cases.** Hutchcroft proves the
  conjecture for several classes, and
  `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` and `fpbs-sc-choi-seo`
  give the percolation conclusion for hyperbolic, nonunimodular and
  acylindrically hyperbolic geometries. **Where it dies:** those proofs use
  the geometric hypothesis directly. Section 3 of the priority assessment
  states as a research judgment, not as evidence, that a general proof may
  isolate their common mechanism and replace the geometry by nonamenability;
  no such mechanism is isolated here.
