---
rg: 2
id: stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1
kind: claim
title: Projection-weight multicopy fibres are Stiefel spaces and strict slack is necessary for uniform loop filling
distinct_from:
  stw22-dim1-factor-bundles-have-uniform-traces: that theorem needs only uniform local path connectedness; the present claim isolates the new loop topology encountered in dimension two.
  stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling: that establishes loop filling in the hyperfinite factor under strict slack; the present claim works in every finite factor, removes the apparent multicopy complication, and proves that the slack cannot be dropped.
artifacts:
  - research/artifacts/stw22-arbitrary-factor-stiefel-boundary-audit-2026-08-30.md
---

Let `N` be a finite factor, let `p in N` be a projection, and let
`s_1,...,s_m` be partial isometries satisfying

```text
s_j^*s_k=delta_(jk)p.
```

Put `q=sum_j s_js_j^*`.  The space of every other such `m`-frame is
canonically isometric, for the Hilbert-sum `2`-metric, to the single Stiefel
space

```text
St_N(q)={V in N:V^*V=q}=U(N)/(q+U((1-q)N(1-q))).
```

Consequently the copy number creates no additional topology.  Under the
maximum tuple metric the same identification is bi-Lipschitz with constants
`1` and `sqrt(m)`.

The strict complement slack in any factor-uniform equi-`LC^1` theorem is
essential.  If equality with the ambient support is allowed, then already

```text
N=M_n,       m=1,       p=1
```

gives the fibre `U(n)`.  The loop

```text
z |-> diag(z,1,...,1)
```

lies in the closed `2/sqrt(n)`-ball about the identity for normalized
Hilbert--Schmidt norm, but is not null-homotopic.  Hence no radius independent
of the finite factor can give local loop fillings at zero slack.

With positive slack, the matrix Stiefel spaces are simply connected, so this
does not refute the desired arbitrary-factor dimension-two theorem.  It
reduces that theorem to a genuinely quantitative, dimension-free filling
radius for `U(N)/U(1-q)` when `tau(1-q)` is bounded below.
