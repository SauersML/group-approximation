---
rg: 2
id: anti-central-ternary-summand-contains-its-matrix-ring
kind: claim
title: The anti-central summand of the ternary Leavitt group algebra contains its own two-by-two matrix ring unitally
distinct_from:
  leavitt-matrix-amplification-in-unit-group-algebra: that embeds matrix algebras over the binary group algebra into supported corners whose identities change; this embeds M_2(S_-) unitally into the anti-central summand of the ternary group algebra, through the diagonal endomorphism and the quaternion subalgebra of the swap and sign units.
  ternary-leavitt-swap-problem-splits-at-central-involution: that splits F_3[G] at the central involution and writes S_- as M_2 of the swap corner; this places M_2(S_-) itself inside S_- with the swap idempotent as E_11 and derives direct-equals-stable finiteness for the summand.
artifacts:
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S = F_3[G]`, `eps_- = 2(1 - [z])`, `S_- = eps_- S`
with unit `1_- = eps_-`, `w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1` and `e_- = 2 eps_-(1 + [w])`.

1. `delta(g) = s0 g t0 + s1 g t1` is an injective endomorphism of `G`. It fixes `z` and commutes
   with `w` and with `d`. Its linear extension is an injective unital endomorphism `delta_*` of
   `S_-`.
2. `Q = span{1_-, [w], [d], [wd]}` is a subalgebra of `S_-` isomorphic to `M_2(F_3)`, with matrix
   units `E_11 = e_-`, `E_22 = 1_- - e_-`, `E_12 = e_- [d]`, `E_21 = [d] e_-`.
3. `delta_*(S_-)` commutes with `Q`, so `J((x_ij)) = sum E_ij delta_*(x_ij)` is an injective unital
   algebra homomorphism `M_2(S_-) -> S_-` with `J(E_11 (x) 1) = e_-`.
4. So `M_(2^n)(S_-)` embeds unitally in `S_-` for every `n`, and `S_-` is directly finite if and
   only if it is stably finite.

Proof: Section 1 of the artifact.
