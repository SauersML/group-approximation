---
rg: 2
id: corona-traces-separate-paradox-from-measure-for-el-n
kind: claim
title: "Corona traces separate paradoxical rings from matricial rings for elementary groups, while the canonical trace is never amenable on either side"
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
