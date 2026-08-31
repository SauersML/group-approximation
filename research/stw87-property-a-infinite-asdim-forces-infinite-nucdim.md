---
rg: 2
id: stw87-property-a-infinite-asdim-forces-infinite-nucdim
kind: claim
title: Property A and infinite asymptotic dimension force infinite uniform Roe nuclear dimension
artifacts:
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
  - research/artifacts/stw87-property-a-ghost-packet-firewall-audit-2026-08-30.md
---

For every countable discrete bounded-geometry metric space `X` with property A
and `asdim(X)=∞`, prove

```text
dim_nuc(C*_u(X))=∞.
```

## Attempts

Sako's theorem only shows that `C*_u(X)` is nuclear, so the nonnuclearity
obstruction used for spaces without property A is unavailable.  The
Winter--Zacharias estimate is one-sided and becomes vacuous at infinity.
Transfinite nuclear-dimension bounds likewise do not give an ordinary nuclear
lower bound.  The coarse-embedding corner reduction would suffice if `X`
coarsely contained spaces with unbounded uniform Roe nuclear dimension, but
no such finite-dimensional seeds beyond value one are known here.
Nor can the property-A kernels themselves turn nuclear approximations into
diagonal-dimension approximations by Schur-localizing the return maps and then
averaging: normalized Schur localization leaves the diagonal expectation
exactly unchanged (`stw87-diagonal-bimodular-localization-no-go`).  Replacing
exact bimodularity by approximate singleton-corner bimodularity does not make
this route perturbative: retaining the basic order-zero packets requires a
fixed defect of at least `1/2`, and of `1` for a matrix packet
(`stw87-approximate-diagonal-bimodularity-order-zero-threshold`).
Single metric-sparsification cutdowns do not evade the threshold: a proper
subset cutdown has norm-one defect from the identity on the global diagonal.
This leaves open multi-corner recombinations, including ones that deliberately
incur the macroscopic defect detected above.
Ghost packets cannot provide a replacement obstruction.  By Roe--Willett,
property A makes every ghost compact, and every finite packet of compact
ghosts admits a zero-colour approximation through one finite coordinate
matrix corner (`stw87-property-a-ghost-packets-are-zero-dimensional`).  In
particular ghosts vanish in the uniform Roe corona.  A successful packet
argument must therefore include non-ghost ambient operators, while a
ghost-based argument must impose a genuinely global uniformity condition not
visible on any one finite packet.
