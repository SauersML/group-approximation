---
rg: 2
id: sparse-free-phase-support-is-a-free-factor
kind: claim
title: Sparse independent free-phase packets have only free-factor support
artifacts:
  - research/artifacts/sparse-free-phase-support-classification-2026-08-21.md
distinct_from:
  britton-support-traps-dense-free-phase-chord: that treats a Fourier-dense packet whose support generates the whole effective phase group; this classifies every sparse zero pattern and shows that its phase support is a free factor.
  free-phase-context-support-is-a-proper-free-factor: that identifies the rank-D-minus-one support of a whole escaped matrix block; this computes the smaller support of one individual sparse packet from its coefficient graph.
  free-factor-phase-graph-hnn-is-residually-finite: that proves residual finiteness once the two edge embeddings are free factors; this proves that every standard independent-phase sparse packet supplies exactly such an embedding.
---

Let `K` be finite, let `q C[K] q` be a full matrix block with matrix units
`(E_(ij))_(1<=i,j<=D)`, and let

```text
F_D=<h_1,...,h_D>,                 W=sum_i h_i E_(ii).   (SFS1)
```

For `Y=sum_(i,j)y_(ij)E_(ij)`, let `G_Y` be the undirected graph on
`{1,...,D}` having an edge `{i,j}`, `i!=j`, exactly when
`y_(ij)!=0` or `y_(ji)!=0`.  If its connected components are
`C_1,...,C_c`, put

```text
H_Y=<h_i h_j^(-1): {i,j} is an edge of G_Y><=F_D.       (SFS2)
```

Then

```text
H_Y is a free factor of F_D of rank D-c,                (SFS3)
WYW^* belongs to q C[K times H_Y]q.                     (SFS4)
```

More explicitly, choose one root `r_alpha` in each component.  The family

```text
{h_(r_alpha):1<=alpha<=c}
 union {h_i h_(r_alpha)^(-1):i in C_alpha, i!=r_alpha}  (SFS5)
```

is a free basis of `F_D`, and the second part of `(SFS5)` is a free basis of
`H_Y`.  Thus a disconnected coefficient graph gives a proper edge support,
and that support is nonamenable precisely when `D-c>=2`; nevertheless it is
still primitive/free-factor support.

Consequently, take two endpoint packets built with independent free-phase
coordinates and transport them term by term with one HNN stable letter,
fixing the finite packet and identifying their phase-difference supports.
Even when sparsity makes both associated subgroups proper and nonamenable,
the phase embeddings are free-factor embeddings.  The resulting cell lies
in the residually finite class of
`free-factor-phase-graph-hnn-is-residually-finite` (with the finite packet
and any old commuting phases absorbed into its auxiliary factor).  It cannot
be the decisive first no-CE signed-Hecke chord.

This does not exclude sparse chords using nonprimitive phase labels,
several coupled stable letters, or a non-HNN algebraic transport.  It proves
that merely choosing a sparse separator-block matrix in the existing
independent-phase regauge only trades the dense whole-support trap for the
already fenced free-factor trap.
