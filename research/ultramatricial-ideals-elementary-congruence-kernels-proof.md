---
rg: 2
id: ultramatricial-ideals-elementary-congruence-kernels-proof
kind: route
title: Localize g into one finite matrix subring B, where GL_n(B) = E_n(B), and embed back by z ↦ (1−e_B)I + z
target: ultramatricial-ideals-have-elementary-congruence-kernels
requires: []
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

The full proof is Lemma B in the artifact.
- **E_n(B) = GL_n(B) for n ≥ 2.** E_n(M_k(F_2)) = SL_{nk}(F_2) = GL_{nk}(F_2).
  - Block elementary matrices give the transvections between different blocks.
  - A transvection inside one block is [t_xy, t_yz] with y in another block.
  - Transvections generate SL, and SL = GL over F_2.
- **Localize.** For g ∈ GL_n(R,I), put x = g − I and y = g^{-1} − I, and choose B containing their entries. Since x + y + xy = 0, e_B I + x ∈ GL_n(B).
- **Embed back.** ι(z) = (1−e_B)I + z is a homomorphism GL_n(B) → GL_n(R) with ι(e_B I + bE_ij) = e_ij(b). So g = ι(e_B I + x) ∈ E_n(I).
- **Local finiteness.** Finitely many elements lie in ι(GL_n(B)) for one B. ∎
