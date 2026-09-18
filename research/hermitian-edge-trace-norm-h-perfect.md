---
rg: 2
id: hermitian-edge-trace-norm-h-perfect
kind: claim
title: The Hermitian edge trace-norm inequality holds for every h-perfect graph, in particular for every perfect graph and every t-perfect graph
artifacts:
  - research/hermitian-edge-trace-norm-h-perfect-proof.md
distinct_from:
  hermitian-edge-trace-norm-k4-free-h-perfect: that proves (**) for h-perfect graphs with omega <= 3 and reduces the rest to the clique inequality; this removes the restriction omega <= 3, using the clique inequality for every m.
  hermitian-edge-trace-norm-vs-independence: that is (**) for every graph; this is the class of h-perfect graphs. Only the non-clique, non-hole STAB facets remain there.
---

**ESTABLISHED (partly computer-assisted: the cases `m = 4, 5` of the clique inequality use exactly
checked branch-and-bound certificates, and `m >= 6` uses an interval-checked LP certificate;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-h-perfect-proof`).**

**Theorem.** Let `G` be an h-perfect graph, meaning `STAB(G)` is cut out by nonnegativity, the clique
inequalities and the odd-cycle inequalities. This class contains every perfect graph and every
t-perfect graph. Then for every `w >= 0` and every Hermitian `C` supported on the edges of `G` with
`|C_ij| >= 1` on edges,

```text
|| D C D ||_1  >=  sqrt3 ( W - alpha_w(G) ),     D = diag(sqrt w).
```

In the language of `hermitian-edge-trace-norm-vs-independence`, the threshold vector of every dual
certificate lies in `STAB(G)`. So (**) is now open only through the STAB facets of general graphs that are
neither cliques nor odd holes (`hermitian-edge-trace-norm-other-stab-facets`).
