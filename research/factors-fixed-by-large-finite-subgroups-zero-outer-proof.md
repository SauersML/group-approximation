---
rg: 2
id: factors-fixed-by-large-finite-subgroups-zero-outer-proof
kind: route
title: Record a fixed generator only on a transversal of a large finite subgroup, then apply subadditivity
target: factors-fixed-by-large-finite-subgroups-have-zero-outer-entropy
requires: [seward-rokhlin-entropy-subadditivity]
artifacts:
  - research/artifacts/rokhlin-kernel-trivial-information-2026-09-12.md
---

Complete proof: Theorem L of the artifact.

1. **The transversal.** `T = T_n` is finite and acts freely, so a Borel transversal `M` exists, with
   `X = ⊔_(t in T) t.M` and `mu(M) = 1/|T|`.
2. **The partition.** Put `alpha = {X \ M} ∪ {B ∩ M : B in beta}`.
   - Since `t^-1.B = B`, `mu(B ∩ M) = mu(B)/|T|`.
   - So `H(alpha) = H(1/|T|, 1 - 1/|T|) + H(beta)/|T|`, which tends to `0` as `n -> infinity`.
3. **Generation.** `B = ⊔_t t.(B ∩ M)`, and every `t.M` is a translate of a union of atoms of `alpha`. So
   `beta ⊆ sigma-alg_W(alpha)` and `F ⊆ sigma-alg_W(alpha)`. Hence `h_W(F) = 0`.
4. **The equality.** `seward-rokhlin-entropy-subadditivity` (Corollary 2.5, two-step form) gives
   `h^Rok_W(X) <= h_W(F) + h_W(X | F) = h_W(X | F)`. Conversely `H(alpha | F) <= H(alpha)` for every
   generating `alpha`.

The model test is Remark 2 of the artifact.
