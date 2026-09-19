---
rg: 2
id: linear-cocycle-dimension-forces-phase-countersequence
kind: claim
title: Linear cocycle dimension turns low-link phases into a Hamming countersequence
distinct_from:
  link-thresholds-need-macroscopic-phase-frustration: that constructs the all-vertex interval-phase family and leaves its quotient distance open; this proves a constant distance lower bound under one explicit cocycle-dimension hypothesis.
  proper-torus-diagonal-code-is-incomplete-cover-curl: that identifies flat diagonal gauges with cellular cocycles; this gives a probabilistic phase construction far from the entire cocycle space, not only from vertex cuts.
  diagonal-parity-is-hecke-but-tau-misses-local-links: that proves collapse of the real link spectral gap; this uses the binary interval geometry and sequential entropy rather than an L2 singular-value estimate.
---

**ESTABLISHED CONDITIONAL COUNTERSEQUENCE.** For

```text
m_n=4^n-1
```

let `K_n=K_(H,m_n)` be the two-triangle proper-label complex, and put

```text
V_n=|V(K_n)|,     E_n=|E(K_n)|=m_n V_n/2,
k_n=dim_(F_2) Z^1(K_n;F_2).                             (LCD1)
```

Assume that for some fixed finite `C`,

```text
k_n<=C V_n                                                    (LCD2)
```

along an infinite sequence of levels. Then there is a constant
`delta_C>0` and, at every sufficiently large level in that sequence, a
choice of translated half-intervals `I_v` in all vertex links such that
the cochain

```text
c_eta({u,v})=1_(I_u)({u,v})+1_(I_v)({u,v})              (LCD3)
```

satisfies

```text
|supp(delta_1 c_eta)|/|G_(m_n)| < 2/n,                  (LCD4)
dist_E(c_eta,Z^1(K_n;F_2)) >= delta_C.                  (LCD5)
```

Thus (LCD2) makes the explicit low-link phase family a genuine binary
Hamming countersequence. In particular, the empirically observed identity

```text
Z^1(K_n;F_2)=B^1(K_n;F_2),                              (LCD6)
```

which would give `k_n=V_n-1`, is more than a classification of exact
codewords: on the levels `m_n` it would **refute** the diagonal Hamming
decoder.

The proof is a sequential entropy argument. Choose an ordering of the
vertices such that, outside a fixed initial fraction, the labels of
earlier neighbors sample every cyclic interval of a fixed positive
relative length. Such an ordering exists by a hypergeometric Chernoff
bound. Process independent uniform interval phases in this order.

For a fixed cocycle `z`, suppose `c_eta` differs from `z` on at most
`delta E_n` edges. At all but a small fixed fraction of vertices, at most
`epsilon m_n` of the backward edges disagree. Once the earlier phases are
fixed, two possible phases at such a vertex must have cyclic distance
`O(epsilon m_n)`; otherwise their two interval indicators disagree on
more than `2epsilon m_n` sampled backward labels. Hence only
`rho m_n` phases remain, where `rho=O(epsilon)`.

After unioning over the exceptional vertices, the number of phase
assignments within `delta E_n` of one fixed `z` is at most

```text
2^V_n rho^((1-beta)V_n) m_n^V_n,                        (LCD7)
```

where `beta<1` and `rho` can be chosen arbitrarily small constants.
There are `2^k_n` cocycles. Under (LCD2), choose the constants so that

```text
2^(C+1) rho^(1-beta)<1.                                 (LCD8)
```

Then the union of all the balls in (LCD7) contains fewer than the
`m_n^V_n` phase assignments. A phase choice outside the union proves
(LCD5), while (LCD4) is the exact interval-boundary estimate already
proved.

No claim that (LCD2) holds is made here. The proper-label cohomology
bound, or a direct substitute controlling the number of cocycles, is now
the exact algebraic gate for converting the low-link mode into a
counterexample. The general diagonal decoder and the non-hyperlinearity
root remain open.

DERIVATION
linear-cocycle-phase-countersequence-proof
