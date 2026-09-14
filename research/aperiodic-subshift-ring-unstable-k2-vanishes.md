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
- **Stable K_2 vanishes (unreviewed).** Use ABC Theorem 3.6 with Lemma 7.2 (`abc-twisted-laurent-k-theory-fibration`) and A = LC(Y,F_2):
  - K_2(A) = colim K_2(F_2)^m = 0 and K_1(A) = colim (F_2^×)^m = 0.
  - So the sequence K_2(A) → K_2(A ⋊ Z) → K_1(A) gives K_2(R_Y) = 0.
  - Lane sk-open-4 derives this for minimal systems as part of its Theorem K (`research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md`: K_2 = 0 over F_2). Regular supercoherence of A is its Step 1, and minimality is not used there.
- **Unstable n = 3 is the gap.** K_2(3, R) → K_2(R) is injective under stable-range bounds (van der Kallen, Suslin–Tulenbaev type), which need sr(R_Y) small. The stable rank of these rings is the question of lanes sk-stable-rank-a/b. Without a bound the conclusion may hold only for large n.
- **Direct tower attempt, dies.** Localize g ∈ ker π_Y into the corner e_V R e_V with V ⊆ X∖Y clopen. The corner contains first-return units, so it is not locally matricial, and GL_n(corner)/E_n(corner) can be nontrivial before stabilization.
- **Surjectivity is enough, and separated limit sets give it (sk-k2-subsystems, unreviewed).**
  - The layer ker π_Y/E_Y is coker(K_2(n,R_X) → K_2(n,R_Y)). So the dictionary at Y needs only surjectivity, not vanishing.
  - `subshift-restriction-kernel-is-relative-elementary` proves ker π_Y = E_n(R_X,I_Y) for n ≥ 2 without any information about K_2(n,R_Y). The hypothesis is that the limit sets of points outside Y ∪ Z lie in Y ∪ Z, for some closed invariant Z disjoint from Y.
  - Why it works: the ideal of the biasymptotic part is a union of finite matrix subrings over F_2 (`biasymptotic-subshift-complement-ideal-is-ultramatricial`, `ultramatricial-ideals-have-elementary-congruence-kernels`).
  - Where it stops: X the orbit closure of a recurrent point x that is not uniformly recurrent, with Y a minimal subset. Corners over V ∋ x have unbounded chains of visits. See `research/artifacts/sk-k2-subsystems-2026-09-13-part1.md` §7.
- **Minimal sets, not limit sets (sk-k2-recurrent, unreviewed).**
  - Bounded visit chains need only that Y contains every minimal subset of X (`subshift-visit-chains-are-bounded-off-every-minimal-subset`). So the kernel equality holds whenever the minimal subsets outside Y form a closed set disjoint from Y (`restriction-kernel-relative-elementary-off-minimal-sets`).
  - That includes orbit closures of recurrent, not uniformly recurrent points with a unique minimal set (`recurrent-orbit-closure-with-unique-sturmian-minimal-set`). The unbounded-chain claim in the previous bullet is false there.
  - Retractions (`equivariant-retract-splits-subshift-el-restriction`) and clopen invariant pieces (`clopen-invariant-complement-el-kernel-is-elementary`) also split.
  - Remaining case: `accumulating-minimal-sets-el-restriction-kernel-elementary`.
