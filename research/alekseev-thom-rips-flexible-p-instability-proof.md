---
rg: 2
id: alekseev-thom-rips-flexible-p-instability-proof
kind: route
title: Apply flexible P-stability quotient permanence inside Wise's residually finite Rips construction
target: hyperbolic-rf-not-flexibly-p-stable
requires:
  - flexible-p-stability-passes-to-fg-normal-quotients
  - sofic-stable-implies-residually-finite
---

Alekseev--Thom, *Remarks on approximability and stability for groups*,
[arXiv:2512.15494v1](https://arxiv.org/abs/2512.15494), Corollary B, gives
exactly the target statement.

For the construction, choose a finitely presented sofic group `Q` which is
not residually finite; the source gives `BS(2,3)` and the
Baumslag--Gersten group as examples. Wise's residually finite Rips
construction supplies a short exact sequence

```text
1 -> N -> G -> Q -> 1
```

in which `G` is hyperbolic and residually finite and `N` is finitely
generated. If `G` were flexibly P-stable, Theorem 2.6 and
`flexible-p-stability-passes-to-fg-normal-quotients` would make `Q`
flexibly P-stable. Since `Q` is sofic,
`sofic-stable-implies-residually-finite` (also Alekseev--Thom Corollary
2.7) would make `Q` residually finite, a contradiction.

## Scope fences

- `N` must be a finitely generated normal subgroup. Finite normal
  generation alone is not the printed hypothesis.
- This is flexible stability in finite symmetric groups with normalized
  Hamming distance, not Hilbert--Schmidt, operator-norm, linear-sofic, or
  C-star-algebra stability.
- Property `(T)` is not used in Theorem 2.6 or Corollary B.
- Corollary B is unconditional. It must not be merged with conditional
  Corollary C, which concerns stability in finite actions and the open
  residual-finiteness problem for hyperbolic groups.

Source status: arXiv preprint v1, submitted 2025-12-17. The theorem,
Corollaries 2.7 and B, and Wise-construction proof were checked from the
primary text on 2026-08-31.
