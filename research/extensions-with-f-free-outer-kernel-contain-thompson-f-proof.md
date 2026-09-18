---
rg: 2
id: extensions-with-f-free-outer-kernel-contain-thompson-f-proof
kind: route
title: The simple group P' acts trivially by outer automorphisms, the centralizer of K is a central extension of P', and the flip-twisted copy of F lifts
target: extensions-with-f-free-outer-kernel-contain-thompson-f
requires:
  - central-extensions-of-thompson-f-contain-f
---

Let `π : G → Q`, and let `P ≤ Q` be isomorphic to `F`. By Brown (arXiv:math/0411347, TeX
l.377--378, quoted in `central-extensions-of-thompson-f-contain-f-proof`), the commutator
subgroup `P'` is simple and contains a subgroup `P_1 ≅ F`.

1. **Trivial outer action on P'.** Conjugation gives `ω : Q → Out(K)`. The image `ω(P')` is
   a quotient of the simple group `P'`, so it is trivial or isomorphic to `P'`. In the second
   case `Out(K)` contains `P_1 ≅ F`, which is excluded. So `ω(P') = 1`.
2. **Central extension.** Let `E = π^{-1}(P')` and `C = C_E(K)`. Every `e ∈ E` acts on `K`
   as some inner automorphism `c_k`, so `k^{-1}e ∈ C`, and `E = KC`. Also `C ∩ K = Z(K)`,
   which is central in `C`. So `1 → Z(K) → C → P' → 1` is a central extension.
3. **Lifting.** Restrict it to `P_1 ≅ F`. By `central-extensions-of-thompson-f-contain-f`
   (a), with `A = Z(K)`, its restriction to the copy `δ(P_1) ≅ F` splits. The section's image
   is a subgroup of `C ≤ G` isomorphic to `F`.

For the consequence about actions, apply the statement with `K` the kernel and `Q = G/K`.
