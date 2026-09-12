---
rg: 2
id: binary-tensor-square-diagonal-norm-localization-proof
kind: route
title: Frobenius onto the Tate quotient, null off-diagonal norms by four orthogonal isometries, then localize at diagonal blocks
target: binary-tensor-square-rank-functions-live-on-diagonal-norms
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

Artifact Section 2.
1. **Lemma 2.1.** `x -> [x ⊗ x]` is additive modulo norms and injective because `R` is simple. The image of
   `B_2` in the Tate quotient is `R`, and `R` has no rank function, so some norm element has positive rank.
2. **Proposition 2.2.** `Sym(u, v)` lies in `B_2` for commuting square-zero `u`, `v`, by summing `g ⊗ g` over
   `{1, 1+u, 1+v, 1+u+v}`.
   - Norms of partial isometries between four disjoint clopen pieces give `T_(ab) S_(cd) = δδ E'`, with ranges
     four orthogonal idempotents below a Thompson conjugate of `E'`. So the rank is `0`.
   - The two slots carry different sets, so no factor `2` appears.
3. **Corollary 2.3.** `1 = Q_P + O_P` with `O_P` null, so `rk z = rk(Q_P z Q_P)`.

*Verification by `w3-vf-linear` (2026-09-12), Section 27.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed: N is an ideal of the flip-fixed algebra, and B_2/(B_2∩N) ≅ R; Sym(u,v) ∈ B_2 by the four-term norm; the four isometries S_ab, T_ab with T_ab S_cd = [a=c][b=d] Sym(p_X', p_Y') and no factor 2; rk E >= 4 rk E; and the localization z − Q z Q null.*
