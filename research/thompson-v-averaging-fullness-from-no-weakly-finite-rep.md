---
rg: 2
id: thompson-v-averaging-fullness-from-no-weakly-finite-rep
kind: route
title: If V has no weakly finite characteristic-two representation, its order-three averaging idempotent is full
target: thompson-v-order-three-averaging-idempotent-is-full
requires:
  - thompson-v-has-no-weakly-finite-char-two-representation
  - rank-condition-rings-have-weakly-finite-images
  - binary-cyclic-corner-full-iff-complement-corner-has-no-state
  - binary-corner-weakly-finite-images-are-unit-representations
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - research/artifacts/thompson-v-weakly-finite-representations-2026-09-16.md
---

Artifact Theorem W_V, the chain (d) => (c) => (b) => (a') => (a). Put `g = (0, 10, 11) -> (10, 11, 0)`,
`e = 1 + g + g²`, `f = 1 - e` and `T_V = f F_2[V] f`.

1. **(d) => (c).** A unital `φ : F_2[V] -> W` into a weakly finite ring has `2 · 1_W = 0`. Its restriction
   to `V` is a group homomorphism into `W^x`, so it is trivial by the first requirement, and `φ(g) = 1`.
2. **(c) => (b).** If `T_V` had a nonzero weakly finite image `q`, Lemma W.2 of
   `research/artifacts/binary-weakly-finite-representations-2026-09-12.md` (the proof of
   `binary-corner-weakly-finite-images-are-unit-representations`, step 1 => 2) gives `φ = q ∘ ψ'` with
   `φ(g) != 1`. That proof uses only `g`, `D`, the units `π_M` and the block idempotents `f_K`. All of
   these lie in `F_2[V]` (artifact Lemma 1.1(3)), so it runs verbatim over `V`.
3. **(b) => (a').** By `rank-condition-rings-have-weakly-finite-images`, `T_V` fails the rank condition. By
   `binary-cyclic-corner-full-iff-complement-corner-has-no-state` (6 => 1), `c e b = 1` is solvable in
   `F_2[V]`. Its artifact records that the proof holds for every `D`-stable subgroup containing `g` and the
   `π_M`, and `V` is such a host (artifact Lemma 1.1(3); `research/artifacts/gk3-binary-fullness-2026-09-14.md`,
   Section 4).
4. **(a') => (a).** `k = (00, 01, 1) -> (0, 10, 11)` satisfies `k h k^(-1) = g`, so `(c k) e_h (k^(-1) b) = 1`
   (artifact Lemma 1.1).

The last requirement places `V` inside `G = L_(F_2)(1,2)^x` through `x -> Σ S[b_i] T[a_i]`, which is injective
because `V` acts faithfully on the sequence module. So `F_2[V]` is `F_2[H]` for the subgroup `H = V <= G`, which
is the setting of the scope sentence of Theorem B.

Simplicity of `V` is not used. The requirements about `R^x` enter only through their proofs, applied at the
host `V`. This scope transfer is the step to check.
