---
rg: 2
id: surjective-endomorphisms-of-braided-v-preserve-pure-part-proof
kind: route
title: Zaremsky's normal subgroup theorem and simplicity of V force surjective endomorphisms to preserve P_br
target: surjective-endomorphisms-of-braided-v-preserve-pure-part
requires:
  - proper-normal-subgroups-of-braided-v-lie-in-pure-part
artifacts:
  - research/artifacts/zp-braided-v-hopfian-2026-09-13.md
---

1. Let `M = phi^{-1}(P_br)`, a normal subgroup of `V_br`. It is proper, since otherwise
   `V_br = phi(V_br) <= P_br`. So `M <= P_br` by
   `proper-normal-subgroups-of-braided-v-lie-in-pure-part`.
2. Composing `phi` with `V_br -> V` gives a surjection with kernel `M`, so
   `V_br/M ≅ V`. `V` is simple (Thompson; recalled on p. 1 of arXiv:1403.8132), so
   `V_br/M` is simple.
3. The projection `V_br/M -> V_br/P_br = V` is onto a nontrivial group, so its kernel
   `P_br/M` is a proper normal subgroup of the simple group `V_br/M`. Hence `P_br = M`.
4. So `ker phi <= phi^{-1}(P_br) = P_br` and `phi(P_br) <= P_br`.
5. For `y` in `P_br`, write `y = phi(x)`. Then `x` lies in `phi^{-1}(P_br) = P_br`, so
   `phi(P_br) = P_br`.
6. The induced map on `V = V_br/P_br` is then a bijection.
