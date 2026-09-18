# gq-stv-host (09-18)
**Approach.** Test the general host G_R = St_N(R) ⋊ V (Leavitt-unit twists), proposed by gq-infinite-primes, against three gates: (a) simple quotients, (b) type (A), (c) FW shells.
**Established.**
- 095dde713 `leavitt-steinberg-thompson-extensions-add-nothing` (+ -proof). V twists are inner and V is acyclic, so G_R ≅ St × V. Normal extensions of a quasisimple input add no simple quotients. Ring symmetries leave K_2 virtually central, so there is no type (A) action. FW shell obstructions pass to K × H when Hom(K,H) = 1. Every GL_n(Q) embeds in PE_3(R_L).
- 9583ec1ad `leavitt-linear-groups-live-in-one-projective-elementary-group`. For Leavitt rings the single group PE_N(R) is the whole question. It holds for L_F2 and fails for R ⊇ Q.
- Attempt 1 added to `st-n-of-r-l-is-generated-by-two-copies-of-itself`.
**Dead.** Every "St_N(R_L) plus ring or Thompson symmetries" host, whether semidirect or a product.
**Needs, for GL_n(Q).** A host containing St_N(R_L) NON-normally in which the central Q^x has infinitely many conjugates, e.g. an element acting on Q^x by a prime shift (the scale-shift gate).
