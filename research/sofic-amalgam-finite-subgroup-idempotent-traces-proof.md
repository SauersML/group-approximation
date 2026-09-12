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
   - Products of two members, and the candidate values `0` and the members themselves, live on
     those rectangles. So the laminar table holds in `F_p[A]`.
2. **Atoms and classes.**
   - Each member has a unique parent: the smallest member above it, or `1`.
   - The atoms `y - sum(children of y)` are orthogonal idempotents defined from the table alone, so
     they lift.
   - Write `d` as a sum of distinct nonzero atoms, and let `d_A` be the sum of the corresponding
     lifted atoms. It is an idempotent with `q(d_A) = d`, hence nonzero.
   - A coefficient expression `c 1 + sum c_i x_i` would not do: members can be linearly dependent
     in `G` and independent in `A`.
   - So `[d] = m [S^n] + sum m_i [x_i]` for integers `m, m_i`, the same integers express `[d_A]`,
     and `t_p([d S^n]) = m n + sum m_i r(x_i)`, where `r(x) = dim(x F_p[H]^n) / |H|`.
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
5. **Sofic realizations (Theorem 2.6).** Let `A -> Gamma` be a homomorphism to a sofic group that
   is injective on the union `U` of the `H_s`.
   - It induces a ring map, so it carries the table and the atoms.
   - It is injective on each `H_s`, so ranks keep their normalization.
   - `d_A` is supported in `U`, so its image stays nonzero.
   - Lemma 2.3 in the image of `A` gives the same conclusion.
6. **Forests (Corollary 2.4).**
   - Along a rooted tree, the free actions of the vertex groups on one finite set can be
     conjugated to agree on the edge groups.
   - The resulting permutation representation of `A` is injective on each vertex group. Its
     kernel acts freely on the Bass--Serre tree, so it is free of finite index.
   - So `A` is virtually free, hence residually finite and sofic. This is the tree version of
     the argument in `two-finite-subgroup-nesting-amalgam-proof`.

Section 1 of the artifact gives an amalgam-free cross-check of the two-subgroup case: a coset
dimension count, `r(e) >= dim V / |D| >= r(f)`, with equality forcing `e S^n = f S^n`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 11 and its addendum in `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the embedding of each `H_i` in `A`, through `A -> G`, and `ι_i(H_i) ∩ ι_j(H_j) = ι(D_ij)`;*
- *rectangle injectivity, and transfer of the table;*
- *the lift through atoms, needed because members may be dependent in `G` and independent in `A`, as step 2 now says;*
- *the density-one free orbits, with `rk(I_n) = n`;*
- *the sofic realizations of step 5, and the forest case.*
