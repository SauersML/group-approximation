---
rg: 2
id: brin-thompson-2v-averaging-fullness-ascends-from-v
kind: route
title: A full order-three averaging idempotent over V stays full over the Brin–Thompson group 2V
target: brin-thompson-2v-order-three-averaging-idempotent-is-full
requires:
  - thompson-v-order-three-averaging-idempotent-is-full
artifacts:
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

That claim uses `h`, with prefix codes `(00, 01, 1) -> (01, 1, 00)`. The prefix replacement `φ` with
`(0, 10, 11) -> (1, 01, 00)` gives `φ g φ^(-1) = h^(-1)`, where `g` is the order-three element
`(0, 10, 11) -> (10, 11, 0)`. Since `e_h = e_(h^(-1))`, `e_h = φ e_g φ^(-1)` in `F_2[V]`, whichever orientation is
used. So `c' e_h b' = 1` gives `(c' φ) e_g (φ^(-1) b') = 1`. The unital ring map `F_2[V] -> F_2[2V]`,
`x -> x ⊗ 1`, carries this to the target
(`research/artifacts/brin-thompson-2v-gottschalk-host-2026-09-12.md`, Section 1).

**Verification (w3-vf-nonlinear, 2026-09-12): valid.** With the operator product of the artifact's Section 1,
tracing `φ^(-1)`, then `g`, then `φ` on `1x`, `01x`, `00x` gives `(1, 01, 00) -> (01, 00, 1)`, which is `h^(-1)`. So
`φ e_g φ^(-1) = e_h`, and the group-ring map of `V -> 2V` carries the solution. Under the opposite product
convention the conjugator is `φ^(-1)` instead. "Whichever orientation is used" covers only how `h`'s codes are
read, and the conclusion holds either way (`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`,
Section 29).
