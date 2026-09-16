---
rg: 2
id: rigid-sft-quotient-fp-from-stable-k2-and-stability
kind: route
title: Gate (b) from finitely generated stable K_2 plus injective stability in some rank at least four
target: rigid-sft-elementary-group-mod-centre-is-fp
requires: [projective-elementary-fp-kernel-criterion, free-minimal-subshift-elementary-groups-are-simple-kazhdan, sft-crossed-product-stable-k2-is-finitely-generated, sft-crossed-product-unstable-k2-injects-stably]
---

Let `Ω` be a free minimal `Z^2`-SFT with `R = LC(Ω, F_q) ⋊ Z^2` finitely presented.

1. **Choose the rank.** By `sft-crossed-product-unstable-k2-injects-stably` there is `n >= 4` with
   `K_2(n,R) -> K_2(R)` injective.
2. **The kernel is finitely generated.** `K_2(R)` is a finitely generated abelian group
   (`sft-crossed-product-stable-k2-is-finitely-generated`). So `K_2(n,R)` is isomorphic to a subgroup
   of it, and is finitely generated. A fortiori it is finitely normally generated in `St_n(R)`.
3. **The centre is finite.** `Z(EL_n(R)) ⊆ F_q^x 1_n` by
   `free-minimal-subshift-elementary-groups-are-simple-kazhdan`, which holds for every `n >= 3`.
4. **Conclusion.** `projective-elementary-fp-kernel-criterion`, with `R` finitely presented and
   `n >= 4`, gives (3) ⟹ (1): `EL_n(R)/Z(EL_n(R))` is finitely presented.

Neither premise is vanishing. `z2-crossed-product-steinberg-kernel-is-nonzero` shows `K_2(n,R) ≠ 0`
in every rank, so the kernel really has to be controlled rather than killed.
