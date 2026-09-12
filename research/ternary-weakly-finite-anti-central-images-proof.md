---
rg: 2
id: ternary-weakly-finite-anti-central-images-proof
kind: route
title: Pull a nontrivial weakly finite representation back along the corner embedding and cut to the minus-one corner
target: ternary-weakly-finite-representations-give-anti-central-images
requires:
  - leavitt-units-embed-in-their-scalar-quotient
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
  - weakly-finite-leavitt-representations-killing-defect-are-trivial
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

Artifact Section 3, Theorem 3.

1. **Minus one moves.** If `rho(z) = -1`, then `rho(z) != 1` because `2` is invertible and `W != 0`.
2. **Defect criterion.** Nontrivial iff `D_rho != 0`, by the weakly finite defect criterion. The trivial
   representation kills `D`.
3. **Normal subgroups.** `PG` is simple and `G` is perfect. So a normal subgroup not contained in `<z>` has
   abelian quotient `G/N`, a quotient of `<z>`, and equals `G`.
4. **Injective pullback.** `ker rho <= <z>` and `iota(G) ∩ {±1} = 1`, so `rho∘iota` is injective.
5. **Corner cut.**
   - `u = rho(iota(z))` is an involution different from `1`.
   - `f = 2(1-u)` is a nonzero idempotent in characteristic three, commuting with `rho(iota(G))`.
   - `x -> f·rho(iota(x))` is a unital ring map into `fWf` with `[z] -> -f`.
   - `fWf` is weakly finite (padding by `1 - f`), and so is the image subring. QED

*Verification by `w4-vf-linear-b` (2026-09-12), Section 36.3 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS, conditional on simplicity of `PG` as recorded on its node. Re-derived independently:*
- *the normal-subgroup trichotomy via perfection;*
- *injectivity of `ρ∘ι`;*
- *`f^2 = 8(1 - u) = f`, the commutation with `ρ(ι(G))`, and `[z] -> fu = 2(u - 1) = -f`, so `eps_+` dies.*
