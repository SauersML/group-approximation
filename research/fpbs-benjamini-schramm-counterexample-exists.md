---
rg: 2
id: fpbs-benjamini-schramm-counterexample-exists
kind: claim
title: Some nonamenable Cayley graph has coinciding percolation thresholds
root: true
distinct_from:
  fpbs-fixed-price-one-percolation-kernel: that is the positive statement for nonamenable fixed-price-one groups, the last case of the cost route; this is the negation of the universal goal, and by Lyons any witness for it must lie inside that same class.
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/spectral-spike.md
  - research/artifacts/fpbs/exploration.md
---

**OPEN; the negation of `fpbs-benjamini-schramm-universal`.** There exist a
nonamenable finitely generated group `Gamma` and a finite symmetric generating
set `S` with

```text
p_c(Cay(Gamma,S)) = p_u(Cay(Gamma,S)).
```

This node exists because of the graph's refutation convention. A
counterexample is not a route into the universal goal; it is an ESTABLISHED
negation claim, and only when this claim is established does
`fpbs-benjamini-schramm-universal` acquire
`refuted_by: [fpbs-benjamini-schramm-counterexample-exists]`.

**The witness class is pinned down.** By Lyons, arXiv:1109.5418, a finitely
generated group without fixed price one has a nonuniqueness phase on every one
of its Cayley graphs. So any witness here is a nonamenable group **of fixed
price one**: it satisfies the Fixed Price assertion for its own group rather
than contradicting it, and it lies inside
`fpbs-fixed-price-one-percolation-kernel`. Section 5 of the forwarded
2026-09-09 priority assessment draws the operational consequence: proving
fixed price one for one more nonamenable group does not advance the
percolation problem, it only moves the group into the class where the cost
obstruction is silent.

It must also avoid every established positive case:
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness` (nonamenable Gromov
hyperbolic quasi-transitive graphs, and graphs with a nonunimodular
quasi-transitive automorphism subgroup) and `fpbs-sc-choi-seo` (every Cayley
graph of an acylindrically hyperbolic group). It must fail Hutchcroft's L2
boundedness conjecture `fpbs-nonamenability-bounds-critical-connectivity-operator`,
so establishing this claim would refute that conjecture too.

## Attempts

* **Show the collapse scenario is internally consistent** (response 9,
  `spectral-spike.md` Sections 4--7). Assuming `p_c=p_u=c`, the note derives
  what collapse forces: a spectral atom of mass `theta(p)^2` at `1` appearing
  immediately above `c`, and conditional pivotal counts of order
  `n exp(alpha n)` for every `alpha<lambda_0/2`. Section 7 then exhibits a
  monotone FIID partition model on the same nonamenable graph that realizes
  exactly this spectral jump, with explicit finite-`n` formulas and a
  logarithmic-derivative peak of rate precisely `lambda_0/2`. **Why this is
  not a counterexample:** Section 7 says so in its own terms. The partition
  classes are not clusters of the ambient Cayley graph. For every `t` in
  `(0,1)` a selected vertex has all `d` neighbours unselected with probability
  `t(1-t)^d>0`, and ergodicity produces such isolated vertices almost surely;
  they belong to the unique infinite class but are not connected to it through
  edges of the graph. The toy parameter also has threshold zero rather than
  `c>0`, so identifying its logarithmic derivative with a Bernoulli pivotal
  count is an error the note names explicitly.
* **Build a nonamenable graph with no indispensable edges** (response 4,
  `creative-branches.md` Section 1.3; response 8, `exploration.md` Section 1).
  The model `H_epsilon` on `T_{2r} x Z` keeps all vertical edges and each
  horizontal edge with probability `epsilon`; it is connected, bridgeless, and
  has divergent mean replacement-route length. **Where it dies:** it is a
  dependent anisotropic law, not Bernoulli percolation on a Cayley graph, and
  Proposition 1 of `exploration.md` shows it is collectively fragile,
  `p_c(H_epsilon) -> 1` as `epsilon` decreases. It separates route length from
  pivotality; it does not produce coinciding thresholds anywhere.
* **Use a cost-one group directly.** Every group in the archive's
  fixed-price-one families (`fpbs-amen2-fixed-price-one`,
  `fpbs-bounded-exponent-two-groups-fixed-price`, `fpbs-sc-fixed-price-family`,
  `fpbs-tfl-fixed-price`) is admissible as a candidate by the Lyons
  constraint. **Where it dies:** admissibility is not a threshold
  computation. For the explicit small-cancellation family the opposite is
  proved, `fpbs-sc-percolation-family` and `fpbs-ew-window` give an actual
  nonuniqueness interval; and the quantitative cost bound of response 1
  degenerates to `0 <= 0` under threshold equality, so it neither forbids nor
  produces a collapse. No candidate has a proved upper bound on `p_u` matching
  a lower bound on `p_c`.
* **Reasoning from the two endpoint facts.** Absence of an infinite cluster at
  `p_c` and absence of a unique cluster at `p_u` are both known and both
  remain true when `p_c=p_u`. Section 8 of `spectral-spike.md` records this
  after a literature check: no implication about strictness may be inferred by
  combining them.
