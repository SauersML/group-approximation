---
rg: 2
id: expander-equality-splitting-is-a-robust-occurrence-four-compiler
kind: claim
title: Expander equality splitting is a dimension-free robust occurrence-four LCS compiler
artifacts:
  - research/expander-equality-poincare-rounding-proof.md
distinct_from:
  cyclic-occurrence-splitting-makes-every-lcs-cubic: that gives the exact occurrence-three Tietze compiler; this replaces its long equality cycles by cubic expanders and proves a uniform normalized-Hilbert--Schmidt decoder.
  degree-two-operator-ports-are-boundary-edges: that locates the exact occurrence-two graph-incidence boundary; this is a quantitative bounded-occurrence compiler for arbitrary LCS presentations.
  one-triple-variable-lcs-has-no-perfect-model-gap: that treats one exceptional triple-used variable exactly; this compiler can split every high-degree variable and makes no perfect-model separation claim.
---

Every finite binary LCS of maximum equation width `w` has an effective,
linear-size compiler to a binary LCS of maximum variable occurrence four
which:

1. preserves the solution group exactly, including the central involution
   `J`;
2. preserves perfect completeness in every operator model; and
3. has a dimension-independent normalized-Hilbert--Schmidt decoder.

For a source variable with `d>=3` occurrences, take the least
`n=6*2^k>=d`, put the occurrences on distinct vertices of a connected
3-regular bipartite Ramanujan graph `H_d` on `n` vertices, and add the
even equality equation

```text
X_u X_v = 1
```

on every edge.  Marcus--Spielman--Srivastava's good 2-lifts give such a
family with

$$
n/d\leq 2,
\qquad
\lambda_*:=1-\frac{2\sqrt2}{3}>0
$$

as a uniform normalized-Laplacian gap.  A used vertex occurs in one source
context and three equality contexts, hence four times; a padding vertex
occurs three times.

Let `N` be the total number of source occurrences.  For reflection-valued
copies in any finite tracial algebra, put

$$
\delta_x^2
 =\frac1{|E(H_x)|}\sum_{uv\in E(H_x)}
   \|X_{x,u}X_{x,v}-I\|_2^2,
\qquad
\varepsilon_{\rm eq}^2
 =\frac1N\sum_{x:d_x\geq3}d_x\delta_x^2 .
$$

There are representative copies `\widehat X_x`, themselves exact
reflections, such that

$$
\frac1N\sum_{\text{source occurrences }(x,u)}
 \|X_{x,u}-\widehat X_x\|_2^2
 \leq \frac{2}{\lambda_*}\varepsilon_{\rm eq}^2.       \tag{1}
$$

If `D_{\rm copy}` is the equation-normalized RMS defect of all source
product relators and all within-source-context commutator relators, and
`D_{\rm dec}` is the same defect after replacing every copy by its
representative, then

$$
D_{\rm dec}
 \leq D_{\rm copy}
      +3w\sqrt{\frac{2}{\lambda_*}}\,\varepsilon_{\rm eq}. \tag{2}
$$

Thus the equality layer loses only an absolute constant (and the unavoidable
source-width factor), independently of dimension and of the original
variable degrees.

The jump from occurrence three to four is sharp for pairwise-equality
splitting.  If every copy already lies in one source equation, occurrence
three leaves equality degree at most two, so a connected equality graph is
a path or cycle.  On \(\mathbb C^2\), the rotating Pauli reflections

$$
R_j=\cos(2\pi j/d)Z+\sin(2\pi j/d)X
$$

have edge equality defect squared `4 sin^2(pi/d)` but average squared
distance exactly `2` from every single reflection.  Hence every such
degree-two synchronization inequality needs a squared constant of order
`d^2`; the cyclic occurrence-three compiler cannot have uniform robust
soundness.

This closes a compiler seam only.  It does not supply the source LCS
separation needed for a non-hyperlinear-group proof.
