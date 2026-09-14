---
rg: 2
id: aperiodic-subshift-ring-unstable-k2-vanishes
kind: claim
title: K_2(n, LC(Y,F_2) ⋊ Z) vanishes for every subshift Y without periodic points and every n ≥ 3
---

**OPEN.** Let Y ⊆ A^Z be a subshift without periodic points (possibly non-minimal, possibly empty) and n ≥ 3.

Claim: the kernel K_2(n, R_Y) of St_n(R_Y) → EL_n(R_Y), where R_Y = LC(Y,F_2) ⋊ Z, is trivial.

With `aperiodic-subshift-el-normal-subgroups-are-sandwiched`, this makes the normal subgroups of EL_n(R_X) exactly the restriction kernels to subsystems.

## Attempts
- **Stable K_2 vanishes (sketch, unverified import).** Use ABC Theorem 3.6 with Lemma 7.2 (`abc-twisted-laurent-k-theory-fibration`) and A = LC(Y,F_2):
  - K_2(A) = colim K_2(F_2)^m = 0 and K_1(A) = colim (F_2^×)^m = 0.
  - So the sequence K_2(A) → K_2(A ⋊ Z) → K_1(A) gives K_2(R_Y) = 0.
  - Still to check: A is regular supercoherent. It is a directed union of the regular rings F_2^m with flat transition maps, so A[t_1..t_p] should be coherent and regular.
- **Unstable n = 3 is the gap.** K_2(3, R) → K_2(R) is injective under stable-range bounds (van der Kallen, Suslin–Tulenbaev type), which need sr(R_Y) small. The stable rank of these rings is the question of lanes sk-stable-rank-a/b. Without a bound the conclusion may hold only for large n.
- **Direct tower attempt, dies.** Localize g ∈ ker π_Y into the corner e_V R e_V with V ⊆ X∖Y clopen. The corner contains first-return units, so it is not locally matricial, and GL_n(corner)/E_n(corner) can be nontrivial before stabilization.
