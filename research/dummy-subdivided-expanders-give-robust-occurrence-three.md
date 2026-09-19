---
rg: 2
id: dummy-subdivided-expanders-give-robust-occurrence-three
kind: claim
title: Dummy-subdivided expanders give a robust occurrence-three LCS compiler
artifacts:
  - research/subdivision-expander-occurrence-three-rounding-proof.md
distinct_from:
  cyclic-occurrence-splitting-makes-every-lcs-cubic: that uses only occurrence-bearing copies on a degree-two equality cycle and is exact but not uniformly robust; this inserts dummy cubic core variables.
  expander-equality-splitting-is-a-robust-occurrence-four-compiler: that places source occurrences directly on cubic expander vertices and spends occurrence four; this places them on edge-subdivision vertices and achieves occurrence three.
  degree-two-operator-ports-are-boundary-edges: that proves maximum occurrence two is graph incidence; this shows the exact jump to occurrence three is also enough for a robust bounded-occurrence compiler.
---

Every finite binary LCS of maximum equation width `w` has an effective,
linear-size compiler to a binary LCS of maximum variable occurrence three
which preserves its entire solution group, fixes `J`, preserves perfect
completeness, and has a dimension-independent normalized-Hilbert--Schmidt
decoder.

For a source variable with `d>=3` occurrences, choose a connected cubic
bipartite Ramanujan graph `H` on the least `h=6*2^k>=d` vertices.  Select
`d` distinct edges and subdivide each selected edge once.  Put one source
occurrence at each subdivision vertex and use all old vertices of `H` as
dummy equality variables.  Equality is tested on every edge of the
subdivided graph `G_d`.

Each used subdivision vertex lies in two equality equations and one source
equation.  Each dummy core vertex lies in three equality equations.  Thus
every variable occurs at most three times.  Connectivity makes all copies
equal in the exact solution group, so Tietze elimination recovers the source
presentation exactly.

Let

$$
\lambda_*:=1-\frac{2\sqrt2}{3},
\qquad
K_*:=16+\frac{112}{3\lambda_*}.
$$

For reflection-valued copies, let \(\delta_x\) be the RMS equality-product
defect over the edges of `G_(d_x)`, let `N` be the total source occurrence
count, and set

$$
\varepsilon_{\rm eq}^2
 =\frac1N\sum_{x:d_x\geq3}d_x\delta_x^2.
$$

There are representative copies \(\widehat X_x\), themselves exact
reflections, satisfying

$$
\frac1N\sum_{\text{source occurrences }(x,u)}
 \|X_{x,u}-\widehat X_x\|_2^2
 \leq K_*\varepsilon_{\rm eq}^2.                        \tag{1}
$$

If `D_copy` and `D_dec` are the equation-normalized RMS defects of every
source product relator and every within-source-context commutator before and
after replacement, then

$$
D_{\rm dec}
 \leq D_{\rm copy}+3w\sqrt{K_*}\,\varepsilon_{\rm eq}. \tag{2}
$$

The constant is absolute, independent of matrix dimension and all source
variable degrees.

Hence occurrence two versus three is not only the sharp exact
expressiveness boundary; occurrence three already supports a uniform robust
pairwise-equality compiler.  The rotating-Pauli lower bound for paths and
cycles remains sharp for the no-dummy construction, but it does not obstruct
a linear-size cubic dummy core.

This compiler does not create the missing perfect
commuting-versus-finite-dimensional source LCS gap.
