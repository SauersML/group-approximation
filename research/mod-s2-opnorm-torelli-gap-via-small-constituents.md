---
rg: 2
id: mod-s2-opnorm-torelli-gap-via-small-constituents
kind: route
title: Find a small prime-to-three Torelli constituent in a near-cube-root representation, then contradict the census limit through its extended determinant
target: mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap
requires:
  - mod-s2-prime-to-three-torelli-constituents-are-large
  - mod-s2-torelli-abelian-census-limit-is-positive
  - mod-s2-cube-root-reps-have-small-prime-to-three-constituents
---

**Route (open because two inputs are open).** Suppose the target fails. Since `Z_hon` is a closed subgroup,
`1/3 in Z_hon`.

1. By `mod-s2-cube-root-reps-have-small-prime-to-three-constituents` (SB), there are honest `rho` with
   `eps < 2` and Torelli constituents of dimension `n` prime to three with `n arcsin(eps/2)` as small as
   wanted. OPEN.
2. By (PC2) of `mod-s2-prime-to-three-torelli-constituents-are-large`, each such constituent has
   `n arcsin(eps/2) >= pi d_inf`. ESTABLISHED.
3. By `mod-s2-torelli-abelian-census-limit-is-positive` (TAP), `d_inf > 0`, which contradicts 1 and 2. OPEN.

**Division of labour and comparison.**
- Step 3 is the arithmetic of relation lattices of separating-twist classes in `H_1` of congruence subgroups.
  It is necessary for the target, by (TA5).
- Step 1 is the representation-theoretic part. It is weaker than the step
  `mod-s2-near-scalar-reps-reduce-to-torelli-abelian` of `mod-s2-opnorm-torelli-gap-via-finite-index-multipliers`.
  That step asks for a whole Torelli-abelian representation; this one asks only for one constituent of dimension
  prime to three and `o(1/eps)`.
- By (PC5) the target is equivalent to steps 1 and 3 together, and each step is also necessary for it.
- (PC6) says step 1 cannot be proved or refuted by determinant data. It needs spectral or structural input
  beyond `n_i mod 3`.
