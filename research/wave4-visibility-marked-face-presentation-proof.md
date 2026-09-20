---
rg: 2
id: wave4-visibility-marked-face-presentation-proof
kind: route
title: Track triangle transports and the face-zero attaching exponent then verify the kernel presentation and its abelianization
target: wave4-visibility-k7-marked-face-presentation
requires:
  - cckw-ghb2-kms-group-structure
  - wave3-canonical-k7-class-has-primitive-evaluation
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-class-two-2026-09-20.md
  - experiments/hrf-wave4-class-two-2026-09-20/vertex_weights.py
  - experiments/hrf-wave4-class-two-2026-09-20/vertex_weights.json
---

Artifact Sections 1-4 give both geometric and algebraic proofs. The
face represented by a^i has corner transports a^i b^-i, b^i c^-i,
c^i a^-i. A maximal edge tree leaves one edge letter T. The zero
face kills T; twisting exactly that face by z instead sets T=z,
and all six remaining relations become r_i=z^-1. Vertex extensions
split uniquely since their groups are finite and Hom(Hj,Z)=0.

For an independent kernel-presentation check, the order-seven
automorphism theta acts by conjugation by a on H0,H2 and by Ad(u1)
followed by conjugation by b on H1. It sends r_i to r_(i+1) modulo
r1; the resulting semidirect product reconstructs G with b=u1^-1 a
and c=w1 a. Thus the six-relator group is exactly K7.

Vertex logarithms have noncentral weights iU_j-i^2 V_j/2, and their
cubic terms are derived. Hence abelianization imposes precisely
sum U_j=sum V_j=0 on six exponent-seven vertex generators. It is
C7^4. Independently, the Schreier presentation has fourteen
generators and seventy relators with exponent-sum rank ten over F7.
