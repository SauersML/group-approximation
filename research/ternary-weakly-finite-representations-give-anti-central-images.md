---
rg: 2
id: ternary-weakly-finite-representations-give-anti-central-images
kind: claim
title: The ternary Leavitt unit group has a nontrivial weakly finite representation iff its anti-central summand has a nonzero weakly finite image
distinct_from:
  ternary-leavitt-rank-models-move-z-iff-nontrivial: that is the equivalence for rank models, including a tensor-square passage to the scalar quotient; this is the equivalence for arbitrary weakly finite target algebras, where only the corner cut along the embedding iota is needed.
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-wf-obstruct`, 2026-09-12; verification requested from
`w4-vf-linear-b`). The step through simplicity of `PG` inherits the condition recorded on
`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`.

Let `G = L_(F_3)(1,2)^x`, `z = -1` and `S_- = eps_- F_3[G]`. A weakly finite representation is a
homomorphism `rho : G -> W^x` into the units of a weakly finite `F_3`-algebra. The following are equivalent:
1. `G` has a nontrivial weakly finite representation;
2. `G` has an injective weakly finite representation;
3. `S_-` has a nonzero weakly finite image (some `rho` has `rho(z) = -1`);
4. some weakly finite representation has `rho(N_23 N_12) != 0`.

**Proof shape** (artifact Theorem 3).
- 3 ⟹ 1 because `-1 != 1`.
- 1 ⟺ 4 by `weakly-finite-leavitt-representations-killing-defect-are-trivial`.
- For 1 ⟹ 2 and 1 ⟹ 3, perfection and simplicity of `PG` give `ker rho <= <z>`. Then `rho∘iota` is injective,
  `u = rho(iota(z))` is an involution different from `1`, and `x -> f·rho(iota(x))` with `f = 2(1 - u)` is an
  anti-central map into the weakly finite corner `fWf`.

DERIVATION
ternary-weakly-finite-anti-central-images-proof
