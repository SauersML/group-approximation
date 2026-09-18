---
rg: 2
id: hermitian-edge-trace-norm-k4-free-h-perfect
kind: claim
title: The Hermitian edge trace-norm inequality holds for every K4-free h-perfect graph (all t-perfect graphs), and odd cycles have exact minimum 2cot(pi/2n)
artifacts:
  - research/hermitian-edge-trace-norm-k4-free-h-perfect-proof.md
  - experiments/hermitian-edge-trace-norm-2026-09-18/README.md
distinct_from:
  hermitian-edge-trace-norm-vs-independence: that is the conjecture (**) for every graph; this proves it for the class of h-perfect graphs with clique number at most 3 (t-perfect graphs, K4-free perfect graphs), which strictly contains the previously known triangle, bipartite and disjoint-union cases, and reduces all h-perfect graphs to the clique inequality.
---

**ESTABLISHED (ordinary proof, unreviewed, not Lean-verified; route
`hermitian-edge-trace-norm-k4-free-h-perfect-proof`).** Notation as in
`hermitian-edge-trace-norm-vs-independence`: `C` is Hermitian, supported on the edges of `G`, with
`|C_ij| >= 1` on edges ("admissible"), `w >= 0`, `D = diag(sqrt w)`, and

```text
(**)     || D C D ||_1  >=  sqrt3 ( W - alpha_w(G) ) .
```

**Theorem A (odd cycles, exact).** For odd `n >= 3` and `C` admissible on the cycle `C_n`,

```text
||C||_1  >=  2 cot(pi/(2n))  >=  sqrt3 (n+1)/2 ,
```

and the first bound is attained (all moduli `1`, flux `n pi/2 mod pi`). Values: `2 sqrt3`, `6.155`,
`8.763`, `11.343` for `n = 3, 5, 7, 9`. The asymptotic ratio to `sqrt3 (n+1)/2` is `8/(sqrt3 pi) = 1.47`.
Proof: a diagonal gauge reduces the phases to one flux; for fixed flux the trace norm is convex and
shift-invariant in the moduli, so uniform unit moduli are optimal; the spectrum is
`2 cos((Phi + 2 pi k)/n)`; for odd `n` the sum of `|cos|` is concave between breakpoints, and its
breakpoint value is `sum_j sin(j pi/n) = cot(pi/(2n))`.

**Theorem B (new class).** (**) holds for all `w >= 0` and all admissible `C` whenever `G` is
**h-perfect with `omega(G) <= 3`**. This includes every **t-perfect** graph (bipartite graphs, odd
cycles, series-parallel graphs, odd-`K_4`-free graphs, ...) and every `K_4`-free perfect graph.
Proof: the threshold vector `y_+`, `y_i = 1 - Q_ii/sqrt3`, satisfies the edge and triangle inequalities
(`2x2` minors; the triangle case) and the induced-odd-hole inequalities (Theorem A applied to the
principal submatrix, or a path-matching count when `y` vanishes somewhere on the hole). Chord
splitting then gives all odd-cycle inequalities, which with the clique inequalities cut out `STAB`.

**Theorem C (strict reduction).** For h-perfect graphs (in particular all perfect graphs), (**) is
**equivalent** to the uniform clique inequality `||C||_1 >= sqrt3 (m-1)` for admissible `C` on `K_m`,
for all `m <= omega(G)`. For general `G`, (**) is equivalent to (**) at the single weight `a` on
`G[S]`, over all full-support nontrivial facets `a` of `STAB(G[S])`. Those facets are cliques
(`hermitian-edge-trace-norm-clique-inequality`), odd holes (Theorem A), and the rest
(`hermitian-edge-trace-norm-other-stab-facets`); see `hermitian-edge-trace-norm-via-stab-facets`.

**What is left.** `K_4` is the smallest graph not covered. The uniform clique inequality for
`m >= 4` is the open core. Numerically it holds with ratio `1.052, 1.044, 1.069, 1.071, 1.089, 1.098`
for `m = 4, 5, 6, 7, 8, 10`.
