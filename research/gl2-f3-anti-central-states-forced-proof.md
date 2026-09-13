---
rg: 2
id: gl2-f3-anti-central-states-forced-proof
kind: route
title: Frobenius reciprocity and a dimension count identify the GL_2(F_3) projective covers with induced semidihedral blocks, and transpose averaging forces the rest
target: gl2-f3-anti-central-states-are-forced-by-semidihedral-blocks
requires:
  - anti-central-k0-states-can-be-chosen-transpose-invariant
  - anti-central-k0-states-equal-lifted-trace-on-signed-thompson
  - anti-central-state-exists-iff-lifted-trace-relatively-positive
  - leavitt-prime-field-units-generated-by-v-and-one-transvection
artifacts:
  - research/artifacts/semidihedral-and-gl2-f3-blocks-forced-states-2026-09-12.md
---

Sections 1 and 2 of the artifact.
- **Lemma 1.1:** `(hw)^4 = z` makes `[hw] eps_-` a root of `x^4 + 1 = p_+ p_-`. Conjugation by `SD` sends `hw` to `hw`
  or `(hw)^3`, and cubing preserves `(p_+)`, so `k_+([hw]) eps_-` is central. It is `1` on the evaluation and `0` on
  the twist, so it is `c_1`.
- **Theorem 1.2:**
  - `V` restricts to the evaluation block, and `V (x) det` to the twisted block, since `det(hw) = -1`.
  - `Ind Q_1` is projective of dimension six and maps onto `V` (Frobenius reciprocity).
  - Projectives have dimension divisible by three, and no character of `GL` is `-1` on `z`, so `P(V) = Ind Q_1`.
  - `P(V)^2 (+) P(V')^2` fills the 24-dimensional block, so there is no third simple module.
  - `alpha_*` exchanges `q_1` and `q_2`, so invariant states give both the value `1/4`.
- **Theorem 2.1:** a state exists by the extension criterion. Average it along `alpha_*`. It equals `trl` on `H_fin(H)`
  and on `H_fin(GL)`, and it is nonnegative on `K_0^+`.
- **Proposition 2.2:** with `n = 1 + s0 t1`, `tau = 1 + s_00 t_00` and the swap `v` of the cylinders `01` and `10`,
  `v n (tau n tau)^(-1) v^(-1) = 1 - s_00 t_01`, and `G = <V, 1 + s_00 t_01>`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 40 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Lemma 1.1, Theorem 1.2, Remark 1.3, Theorem 2.1 and Proposition 2.2 re-derived on paper, and the displays match. Not decision-level: no trace-lowering relation is constructed, and `anti-central-lifted-trace-is-relatively-positive` stays OPEN.*
