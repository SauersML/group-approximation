---
rg: 2
id: kt-full-double-cstar-not-mf-proof
kind: route
title: Retain one strict Kazhdan compressor in a vertex of the double
target: kt-full-double-cstar-is-not-mf
requires:
  - maximal-group-cstar-infinite-under-strict-compression
  - kt-two-positive-compressors-generate-full-obstruction
artifacts:
  - GroupApproximation/Analysis/MaximalCStarParagraphEndpoint.lean
  - GroupApproximation/Analysis/MaximalGroupCStar.lean
---

Use the `q=2`, `d=3` instance of the second prerequisite and take
`t=I+E_12`.  It gives

```text
t Gamma t^(-1)<Gamma,
```

with `Gamma` Kazhdan.  Bass--Serre normal form makes each canonical map
`G->D=G *_Gamma G` injective, so this is the same strict subgroup inclusion
inside `D`; no C-star-algebra injectivity assertion is being assumed here.

Apply `maximal-group-cstar-infinite-under-strict-compression` with ambient
group `E=D`.  Its Kazhdan projection `p in C*(D)` satisfies

```text
(u_t p u_t^*)p=p=p(u_t p u_t^*),       u_t p u_t^* != p.
```

This is a proper projection compression, hence a proper-isometry witness.
Consequently `C*(D)` is not Dedekind finite, not stably finite, has no MF
embedding, and is not MF.

For clarity, this also directly contradicts `(RAT1)` of
`reduced-amalgam-canonical-trace-is-mf`: asymptotic multiplicativity and
asymptotic full-norm isometry would send `a` to `[phi_n(a)]` and define an
injective star homomorphism from `C*(D)` to the norm matrix corona.  The trace
convergence in `(RAT1)` is irrelevant to the contradiction.
