---
rg: 2
id: algebraic-subshift-rigidity-proof
kind: route
title: Spread one ideal relation by right translation until its windows are disjoint
target: full-shift-maps-into-two-sided-algebraic-subshifts-are-constant
requires: []
artifacts:
  - research/artifacts/gottschalk-table-realization-and-evasion-2026-09-12.md
---

Derivation: Section 2 of the linked artifact.

- **One relation.** Write the map as `F(y)(x) = f(y|_(xD))`. Take a nonzero `r` in
  `I` with support `a_1, ..., a_n` and coefficients `c_i`. Since `rk` lies in `I`,
  `sum_i c_i f(y|_(a_i k D)) = 0` for every `y` and every `k`.
- **Disjoint windows.** The windows `a_i k D` and `a_j k D` meet only for `k` in a
  finite union of right cosets of the centralizer of `a_i^-1 a_j`. In an icc group
  that centralizer has infinite index. By B. H. Neumann's lemma, some `k` avoids
  every one of these cosets.
- **Conclusion.** For that `k` the windows are disjoint, so `sum_i c_i f(b_i) = 0`
  for independent inputs `b_i`. Hence `f` is constant.
- **Leavitt instance.** It needs only `[1] + [g] + [g^2]` in the kernel, and the
  simplicity of the unit group.
