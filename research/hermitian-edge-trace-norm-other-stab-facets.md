---
rg: 2
id: hermitian-edge-trace-norm-other-stab-facets
kind: claim
title: The Hermitian edge trace-norm inequality holds at every full-support stable-set facet that is neither a clique nor an odd hole
artifacts:
  - experiments/hermitian-edge-trace-norm-2026-09-18/README.md
distinct_from:
  hermitian-edge-trace-norm-vs-independence: that is (**) for all graphs and weights; this is (**) only at single facet weights (H, a) of full support other than cliques and odd holes, which together with the clique inequality is equivalent to it.
  hermitian-edge-trace-norm-clique-inequality: that is the clique facets; this is every other non-hole facet.
---

**OPEN (conjecture; numerics).** Let `H` be a graph and `a > 0` on `V(H)` such that
`a . x <= alpha_a(H)` is a facet of `STAB(H)`, and `(H, a)` is neither (a complete graph, `a = 1`) nor
(an odd hole, `a = 1`). Then for every admissible `C` on `H` (Hermitian, supported on edges, moduli
`>= 1`), with `D = diag(sqrt a)`,

```text
|| D C D ||_1  >=  sqrt3 ( a(V(H)) - alpha_a(H) ) .
```

**Why it matters.** With `hermitian-edge-trace-norm-clique-inequality` and the odd-hole case
(proved in `hermitian-edge-trace-norm-k4-free-h-perfect`), this implies (**) for every graph, by the
facet reduction (`hermitian-edge-trace-norm-via-stab-facets`). It is vacuous for h-perfect graphs.

**Examples and numerics** (`experiments/hermitian-edge-trace-norm-2026-09-18/facet_min.py`, local
minimization): odd antiholes `C̄_7` (ratio `1.189`), `C̄_9` (`1.108`); wheels `W_5` with hub weight `2`
(`1.157`), `W_7` with hub weight `3` (`1.239`); webs `C_8^2` (`1.155`), `C_11^3` (`1.185`),
`C_7^2` (`1.189`), `C_10^3` (`1.209`). The smallest ratio seen is at the antihole `C̄_9`; antiholes
contain large cliques, which is where the tension concentrates.
