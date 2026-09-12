---
rg: 2
id: sofic-amalgam-finite-subgroup-idempotent-traces-proof
kind: route
title: Transfer the laminar multiplication table to the intersection amalgam and evaluate a faithful sofic rank normalized on finite subgroups
target: sofic-amalgam-finite-subgroup-idempotent-traces-are-strict
requires:
  - lifted-trace-detects-finite-subgroup-projectives
artifacts:
  - research/artifacts/finite-subgroup-combination-defects-2026-09-12.md
---

The complete proof is Section 2 of the attached artifact. Outline:

1. **Transfer (Lemma 2.2).**
   - Each `H_i` embeds in the intersection amalgam `A`, and `H_i n H_j = D_ij` there, because
     `A -> G` restricts to the inclusions.
   - An equality `ab = a'b'` in `G` with `a, a' in H_i` and `b, b' in H_j` forces
     `a'^(-1) a = b' b^(-1) in D_ij`, which holds already in `A`. So `A -> G` is injective on every
     rectangle `H_i H_j`.
   - Products `x_i x_j`, and the candidate values `0`, `x_i`, `x_j`, live on those rectangles, so
     the laminar table holds in `F_p[A]`. The lift `d_A` of `d` is a nonzero idempotent.
2. **Classes.** Each family member has a unique parent, the smallest member above it or `1`. The
   atoms `y - sum(children of y)` are orthogonal idempotents, and every laminar combination is a
   sum of atoms. So `[d] = m [S^n] + sum m_i [x_i]` for integers `m, m_i`, the same integers
   express `[d_A]`, and `t_p([d S^n]) = m n + sum m_i r(x_i)`, where
   `r(x) = dim(x F_p[H]^n) / |H|`.
3. **Sofic rank (Lemma 2.3).** Take the Elek--Szabo rank function `rk` of a sofic approximation
   of `A`.
   - It is additive on orthogonal idempotents.
   - It is faithful: greedily choose points whose `Sigma`-translates are distinct and separated.
     This gives linear independence and linear rank.
   - It equals `r` on idempotents of finite subgroups. The approximation acts freely and exactly
     on a density-one union of regular `H`-orbits, where the permutation module is free over
     `F_p[H]`.
4. **Conclusion.** `rk(d_A) = m n + sum m_i r(x_i) = t_p([d S^n])`, and faithfulness makes it
   positive. A Kaplansky defect has class zero and lifted trace zero, so `d` is not one.
5. **Forests (Corollary 2.4).**
   - Along a rooted tree, the free actions of the vertex groups on one finite set can be
     conjugated to agree on the edge groups.
   - The resulting permutation representation of `A` is injective on each vertex group. Its
     kernel acts freely on the Bass--Serre tree, so it is free of finite index.
   - So `A` is virtually free, hence residually finite and sofic. This is the tree version of
     the argument in `two-finite-subgroup-nesting-amalgam-proof`.

Section 1 of the artifact gives an amalgam-free cross-check of the two-subgroup case: a coset
dimension count, `r(e) >= dim V / |D| >= r(f)`, with equality forcing `e S^n = f S^n`.
