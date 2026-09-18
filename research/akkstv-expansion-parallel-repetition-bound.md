---
rg: 2
id: akkstv-expansion-parallel-repetition-bound
kind: claim
title: A bipartite unique game of value at most 1-eps whose question graph has normalized spectral gap lambda has r-fold parallel value at most (1 - Omega(eps lambda / log(1/eps)))^r, proved through the Feige--Lovasz SDP sigma (AKKSTV 2008, Theorems 4.1 and 4.3)
distinct_from:
  unique-games-on-expanding-constraint-graphs-are-easy: that imports the rounding algorithm (Theorems 1.1, 2.4, 2.6, 3.2) of the same paper; this imports its Section 4 parallel-repetition bound, a statement about values of repeated games that uses the rounding only inside its proof.
  raz-odd-cycle-repetition-lower-bound: that is a lower bound on repeated values of one non-expanding game; this is an upper bound valid on all expanding question graphs.
  dinur-steurer-projection-game-repetition-bound: that is a universal bound for projection games independent of expansion; this bound depends on the spectral gap and is linear in eps rather than quadratic.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that kills universal bounds; this is the standard instance of the expansion-dependent survivor named there.
---

**ESTABLISHED, BY CITATION.** Arora, Khot, Kolla, Steurer, Tulsiani and
Vishnoi, *Unique Games on Expanding Constraint Graphs are Easy*, STOC 2008,
Section 4. Verbatim text and the reading used here are in the route.

*Form used in this graph.* There is an absolute constant `c_R` in `(0, 1/2]`
with the following property. Let `U` be a bipartite unique game (two-prover,
one-round) with question graph `G`. Let `λ` be the second smallest eigenvalue of
the normalized Laplacian of `G`, so `λ` is `1 − λ_2` for the constraint walk
of `U`. Suppose `opt(U) <= 1 − ε` with `0 < ε <= 1/e`. Then, for every `r >= 1`,

```text
opt(U^(⊗r))  <=  σ(U)^r  <=  (1 − c_R ε λ / ln(1/ε))^r .
```

Here `σ` is the value of the Feige--Lovász SDP (Figure 3 of the paper). The
first inequality is Theorem 4.1 (Feige--Lovász). The second inequality is the
proof of Theorem 4.3.

Credit is the authors'. Nothing is reproved here.

DERIVATION akkstv-expansion-parallel-repetition-citation
