---
rg: 2
id: gal-configuration-space-euler-characteristic-formula-citation
kind: route
title: "Import Gal, Theorem 2: generating function for Euler characteristics of configuration spaces of complexes"
target: gal-configuration-space-euler-characteristic-formula
requires: []
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part3.md
---

Citation import. Ś. R. Gal, *Euler characteristic of the configuration space
of a complex*, arXiv:math/0202143, Colloq. Math. 89 (2001). Verbatim:

- Definition: "eu_X(t) := Σ χ(C_n(X)) t^n/n!";
- Theorem 2: "Let X be a complex. For any cell σ let d_σ and v_σ denote
  respectively the dimension of σ and the Euler characteristic of the normal
  link L_σ of σ. Then eu_X(t) = Π_σ (1 + (−1)^{d_σ}(1 − v_σ)t)^{(−1)^{d_σ}}."

Specialization to graphs: a vertex has `d = 0` and `v = deg`; an edge has
`d = 1` and `v = 0`. Unordered counts divide by `n!`. Read from the arXiv
PDF on 2026-09-13. Sanity checks on the arc, circle and triod: artifact
part 1.
