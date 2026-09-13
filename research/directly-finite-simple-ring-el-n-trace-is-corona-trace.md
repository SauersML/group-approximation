---
rg: 2
id: directly-finite-simple-ring-el-n-trace-is-corona-trace
kind: claim
title: "Is the canonical trace of EL_n over a finitely generated simple directly finite ring always an MF trace?"
distinct_from:
  corona-traces-separate-paradox-from-measure-for-el-n: that proves the separation on paradoxical, matricial and subshift rings; this asks whether direct finiteness alone suffices outside those classes.
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**OPEN.** Let R be a finitely generated simple unital ring that is directly finite, and n ≥ 3. Is the
canonical trace of EL_n(R) a corona trace, in the sense of `lef-group-canonical-trace-is-a-corona-trace`?

**What is known.**
- **Necessity.** A corona trace forces EL_n(R) to be MF (`lef-group-canonical-trace-is-a-corona-trace` (a)).
  For simple R, an MF EL_n(R) forces R to be directly finite (`non_mf_groups_exist.tex` Cor l.1016).
- **Stable finiteness.** If some M_m(R) fails direct finiteness, every corona trace is trivial for N ≥ 2m
  (`corona-traces-separate-paradox-from-measure-for-el-n` (i)). So the question is really about stably
  finite R.
- **Positive cases.** Matricial rings over finite fields, and all subshift rings, by (ii) and (iii) there.

## Attempts

- **Trace control from bare MF (2026-09-13, un-traces).** Operator-MF approximations Θ need not realize
  δ_e. Tensor powers Θ^{⊗m} kill |tr_ω Θ(g)| < 1, but not deviations that are operator-large and HS-small
  (low rank), since then tr_ω Θ(g) = 1. Such deviations do occur for corona representations of
  non-Kazhdan groups (`corona-hs-radical-is-finite-residual`). So "MF ⟹ corona trace" needs a mechanism
  that promotes rank-null detection to trace detection. None is known.
- **Characteristic 0 (2026-09-13, un-traces).** A unital embedding of R into ∏_ω M_N(C) gives linear models
  in GL_N(C), not unitary ones, so §4(b) does not apply. The corona-trace route through (ii) needs finite
  fields.
- **Stably finite without towers (2026-09-13, un-traces).** No candidate ring is known that is stably finite
  and simple, has no matricial rank function, and still has a (T) elementary group. The middle rings of
  un-middle (type semigroups that are not almost unperforated) are the natural test class.

**Naming and credit (review 2026-09-13, un-verify-measure, relaying un-novelty).** A *corona trace* is exactly an MF trace in the sense of C. Schafhauser, *MF traces and the Cuntz semigroup*, arXiv:1705.06555. Its abstract, read at review: "A trace τ on a separable C*-algebra A is called matricial field (MF) if there is a trace-preserving morphism from A to Q_ω". For separable C*_max(G) the two definitions agree, and the graph's MF-trace nodes (`hyperlinear-trace-not-mf-trace`, `faithful-mf-models-realize-all-mf-traces`) use the same notion. Node ids keep the word `corona`; read it as MF trace.

**Review (un-verify-measure, 2026-09-13): display checked (OPEN node).** The necessity bullet is correct; naming paragraph added. See `research/artifacts/un-review-measure-2026-09-13-part2.md` §T6.
