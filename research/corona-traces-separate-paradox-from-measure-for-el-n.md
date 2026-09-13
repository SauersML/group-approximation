---
rg: 2
id: corona-traces-separate-paradox-from-measure-for-el-n
kind: claim
title: "MF traces separate paradoxical rings from matricial rings for elementary groups, while the canonical trace is never amenable on either side"
distinct_from:
  full-complementary-idempotent-elementary-full-mf-radical: that is the group-level non-MF theorem for full defects; this is its trace-level consequence placed next to the matricial side.
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let R be a countable unital ring.
- **(i) Paradox.** If 2m[1] ≤ m[1] in V(R) and N ≥ 2m, every corona trace on C*_max(EL_N(R)) is the trivial
  character. In particular, for R ≠ 0 the canonical trace of EL_N(R) is not a corona trace.
- **(ii) Measure.** If R embeds as a unital subring of an algebraic ultraproduct ∏_ω M_{N_k}(F_{q_k}) of
  matrix algebras over finite fields, the canonical trace of EL_N(R) is a corona trace for every N ≥ 1.
- **(iii) Subshift rings.** For a finite-alphabet subshift X, R_X = LC(X,F_q)⋊Z and n ≥ 4:
  τ_{EL_n(R_X)} is a corona trace ⟺ EL_n(R_X) is MF ⟺ R_X is directly finite.
- **(iv) Blind spot.** For finitely generated simple infinite R and n ≥ 3, τ_{EL_n(R)} is never amenable,
  on either side (`elementary-group-trace-amenable-iff-ring-residually-finite`).

So at the level of traces the paradox/measure dichotomy behind the non-MF paper (Leavitt side) and the
Pestov 9.1 answer (subshift side) is detected by corona traces, and is invisible to amenable or
quasidiagonal traces.

Proof route: `corona-traces-separate-paradox-measure-proof`.

**Naming and credit (review 2026-09-13, un-verify-measure, relaying un-novelty).** A *corona trace* is exactly an MF trace in the sense of C. Schafhauser, *MF traces and the Cuntz semigroup*, arXiv:1705.06555. Its abstract, read at review: "A trace τ on a separable C*-algebra A is called matricial field (MF) if there is a trace-preserving morphism from A to Q_ω". For separable C*_max(G) the two definitions agree, and the graph's MF-trace nodes (`hyperlinear-trace-not-mf-trace`, `faithful-mf-models-realize-all-mf-traces`) use the same notion. Node ids keep the word `corona`; read it as MF trace.

**Scope (review 2026-09-13).** This separation is a trace-level reading of `non_mf_groups_exist.tex` Thm l.918 (through `stably-infinite-ring-elementary-groups-have-no-mf-quotient`) and of LEF embeddings, stated with MF traces. It is not a new invariant.

**Review (un-verify-measure, 2026-09-13): PASS on (ii)–(iv); (i) CONDITIONAL.** (i) rests on the unreviewed `stably-infinite-ring-elementary-groups-have-no-mf-quotient` (case n = 1 is `full-defect-ring-non-mf-at-rank-two`). Manuscript Lemma `prop:mf-residual-calculus` is checked verbatim at the tip. Naming and scope corrected. See `research/artifacts/un-review-measure-2026-09-13-part2.md` §T5.
