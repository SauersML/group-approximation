---
rg: 2
id: anti-central-lifted-trace-is-relatively-positive
kind: claim
title: The lifted trace is nonnegative on every positive K_0 class of the ternary anti-central summand spanned by signed-Thompson finite-subgroup projectives
refuted_by:
  - ternary-anti-central-unit-class-is-nonpositive
  - ternary-anti-invariant-swap-corner-is-full
distinct_from:
  anti-central-state-exists-iff-lifted-trace-relatively-positive: that proves this condition is equivalent to the existence of a state; this asserts the condition.
  lifted-trace-detects-finite-subgroup-projectives: that constructs the additive lifted trace and proves it is nonzero on finite-subgroup projectives; this asks for positivity on ambient positive classes in their span.
  ternary-leavitt-units-have-a-nontrivial-char-three-rank-model: that asks for a rank model, which gives a state and hence this condition; this asks only for positivity of one explicit invariant, with no approximation.
artifacts:
  - research/artifacts/lifted-trace-state-extension-2026-09-12.md
---

**OPEN.** Let `R = L_(F_3)(1,2)`, `G = R^x`, `S_- = eps_- F_3[G]`, `H = E x| V` the signed Thompson group, and `trl` the
normalized lifted trace `2 dim/|K|` on idempotent matrices over `eps_- F_3[K]`, `K <= H` finite with `z in K`.

Claim: for all finite direct sums `P`, `Q` of such projectives and every finitely generated projective `X` over `S_-`,

    P (+) S_-^r ~= Q (+) X (+) S_-^r   implies   trl(P) >= trl(Q).

Equivalently, `trl >= 0` on `H_fin(H) ∩ K_0^+(S_-)`, where `trl` is well defined on `H_fin(H)` by the additive lifted
trace.

**Equivalent forms** (`anti-central-state-exists-iff-lifted-trace-relatively-positive`):
- `(K_0(S_-), [eps_-])` admits a state;
- `ternary-anti-invariant-swap-corner-is-full` fails;
- `ternary-anti-central-unit-class-is-nonpositive` fails.

**Why it matters.** It is the obstruction side of the ternary counterexample route, stated through one invariant that
is already defined everywhere. The additive lifted trace `s_3 : K_0(S_-) -> Z_3` obeys every known state law: Haar
measure on clopens, the lifted trace on all finite subgroups, halving and transpose invariance. What this claim needs
is nonnegativity, and only on classes in the span of signed-Thompson finite-subgroup projectives.

## Attempts

- *Well-definedness is free* (lane w4-trace-state, artifact Section 1). No equality relation among finite-subgroup
  projectives lowers the lifted trace, because `s_3` is additive on `K_0`. So a counterexample has to be a stable
  isomorphism with a complement `X` of negative lifted trace. A corner witness gives `X = h S_-` with `s_3([h]) = -1/2`.
- *Finite-support lifts are positive* (artifact Remark 3.1). If a class has an idempotent lift of finite support over
  `Z_3[G]` and a rational lifted trace, that trace lies in `[0, 2n]`: embed the coefficient field in `C` fixing `Q` and
  apply Kaplansky positivity. The complement `X` of a counterexample has negative rational lifted trace, so it has no
  finite-support lift. The failure has to be genuinely modular.
- *Where it stops.* No positivity principle is known for `Z_3`-valued traces of infinite-support idempotent lifts.
  - *Power formula.* `s_3` modulo `3^(k+1)` is the identity coefficient of `x^(3^k)` for any lift `x` (artifact
    Remark 3.2). That is arithmetic, and it carries no order.
  - *Rank functions.* A rank function would give positivity, and none is known on `S_-`.
- *Semidihedral and `GL_2(F_3)` blocks* (lane w6-wf-stage1-b, artifact
  `semidihedral-and-gl2-f3-blocks-forced-states-2026-09-12.md`). The anti-central projectives of `GL_2(F_3)` are induced
  from the two semidihedral blocks, which transpose averaging balances. So relative positivity over `H`, `SD` and
  `GL_2(F_3)` is equivalent to positivity over `H` (`gl2-f3-anti-central-states-are-forced-by-semidihedral-blocks`).
  `H` and `GL_2(F_3)` generate `G`, so positivity over the group they generate is the stronger extension of the whole
  lifted trace. Neither semidihedral block is full (`semidihedral-anti-central-blocks-are-not-full`), but that does not
  survive stabilization. Where it stops: `alpha` fixes the self-dual anti-central simple modules of `GL_3(F_3)`, so
  averaging forces nothing there.
- *Spectral weights and `GL_3(F_3)`* (lane w7-gl3-f3-states, artifact
  `gl3-f3-anti-central-spectral-states-2026-09-12.md`; all OPEN pending `w4-vf-linear-b`).
  - Three-regular units of `G` are conjugate iff they have the same minimal polynomial, and they are conjugate into
    `H` iff it is binomial (`three-prime-leavitt-units-classified-by-minimal-polynomial`).
  - So a state is one weight `W_s` on minimal polynomials, forced to the lifted trace exactly at binomial ones
    (`anti-central-states-are-forced-exactly-on-binomial-spectra`).
  - `GL_3(F_3)` has six non-binomial anti-central directions, and three real weights survive `alpha` averaging. The
    lifted trace extends positively over `H` and `GL_3(F_3)` iff some state has those weights zero
    (`gl3-f3-alpha-invariant-states-keep-three-free-spectral-weights`).
  - No `GL_3(F_3)` projective lowers the lifted trace. The GL_2 averaging argument cannot reach `GL_n` for `n >= 3`,
    since the finite data admit other states there.
  - Where it stops: forcing a non-binomial weight needs `K_0` relations, or positivity, through elements of infinite
    order.
