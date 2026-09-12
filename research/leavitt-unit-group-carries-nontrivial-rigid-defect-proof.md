---
rg: 2
id: leavitt-unit-group-carries-nontrivial-rigid-defect-proof
kind: route
title: A central conjugate of Thompson's V would be abelian
target: leavitt-unit-group-carries-nontrivial-rigid-defect
requires:
  - openai-nine-leaf-leavitt-configuration
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

The configuration gives:

- `[Gamma, J] = 1`, so `J <= C_(R^x)(Gamma)`;
- `u J u^-1 = V_(0001) <= Gamma`;
- `J ~= V`.

Suppose every commutator `[u j u^-1, gamma]` with `j in J` and
`gamma in Gamma` were trivial. Then

```text
V_(0001) = u J u^-1 <= Gamma cap C(Gamma) = Z(Gamma),
```

so `V_(0001)` would be abelian. But it is isomorphic to Thompson's `V`, which
is nonabelian: for example, two cylinder transpositions with overlapping
supports do not commute. So some such commutator is nontrivial.

**Not normal.** If `Gamma` were normal in `G_L`, every element of `G_L` would
normalize `Gamma` and therefore `C(Gamma)`. Then `g z g^-1` would centralize
`Gamma` for every `z in C(Gamma)`, and the defect would vanish. ∎
