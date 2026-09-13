---
rg: 2
id: braided-thompson-v-is-hopfian-proof
kind: route
title: bV is Hopfian because surjections restrict to P_br and stabilizing graded kernels meet a residually nilpotent group
target: braided-thompson-v-is-hopfian
requires:
  - surjective-endomorphisms-of-braided-v-preserve-pure-part
  - pure-braided-thompson-group-is-residually-nilpotent
  - braided-v-graded-pure-quotients-are-noetherian
artifacts:
  - research/artifacts/zp-braided-v-hopfian-2026-09-13.md
---

Artifact §5.

1. Let `phi` be a surjective endomorphism of `V_br`. By
   `surjective-endomorphisms-of-braided-v-preserve-pure-part`, `psi = phi|P_br` is a
   surjective endomorphism of `P_br` with `ker psi = ker phi`.
2. `psi(gamma_c(P_br)) = gamma_c(P_br)`, so `psi` induces surjections
   `psi_c: gr_c -> gr_c`, where `gr_c = gamma_c(P_br)/gamma_{c+1}(P_br)`.
3. Since `psi(x p x^{-1}) = phi(x) psi(p) phi(x)^{-1}` for `x` in `V_br`, the kernel
   `K_j = ker(psi_c^j)` is invariant under conjugation by `V_br`, hence `V`-invariant.
4. By `braided-v-graded-pure-quotients-are-noetherian`, `K_1 <= K_2 <= …` stabilizes,
   say `K_j = K_{j+1}`. If `v` is in `K_1`, write `v = psi_c^j(w)`. Then
   `psi_c^{j+1}(w) = 0`, so `w` is in `K_{j+1} = K_j` and `v = 0`. Every `psi_c` is
   injective.
5. Let `p ≠ 1` in `P_br`. By `pure-braided-thompson-group-is-residually-nilpotent` there
   is `c` with `p` in `gamma_c(P_br) \ gamma_{c+1}(P_br)`. Its class in `gr_c` is nonzero,
   so `psi_c` of it is nonzero and `psi(p) ≠ 1`.
6. So `ker phi = 1`.
