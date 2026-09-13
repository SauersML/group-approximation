---
rg: 2
id: leavitt-unit-hosts-exclude-matrices-over-commutative-rings
kind: claim
title: Leavitt unit groups over prime fields have no nontrivial hosts inside matrices over commutative rings
distinct_from:
  leavitt-unit-hosts-need-nilpotents-of-unbounded-index: that uses unipotence of p-power elements and covers rings of bounded nilpotence index; this uses residual finiteness of finitely generated linear groups and covers matrices over commutative rings whose nilpotents have any index.
  finitely-generated-linear-groups-are-residually-finite: that is Malcev's theorem over fields; this uses its version over commutative rings to exclude the Leavitt unit groups from GL_n(C) for every nonzero commutative C, reduced or not.
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w6-wf-construct`, 2026-09-12). It imports Malcev's theorem over commutative rings
at statement level; a proof sketch is in the artifact. Verification is requested from `w4-vf-linear-b`.

Let `C` be a nonzero commutative ring and `n >= 1`.
1. Every homomorphism `L_(F_2)(1,2)^x -> GL_n(C)` is trivial.
2. If `3·1 = 0` in `C`, no homomorphism `G_3 = L_(F_3)(1,2)^x -> GL_n(C)` sends `z = -1` to `-1`.

**Why.**
- Both groups are finitely generated.
- Finitely generated subgroups of `GL_n(C)` are residually finite, so the image is a residually finite quotient.
- The only quotients are the group itself, `G_3/{±1}` in the ternary case, and `1`. The nontrivial ones are
  infinite and have no proper finite-index normal subgroup, so the image is trivial.

**Scope.** This covers `GL_n(C)` for non-reduced `C` of any nilpotence, and `∏_i M_n(C_i)` at fixed `n`. Growing `n`
is not covered.

**PI hosts.** Artifact Remark B.2 extends the result to every PI host, conditional on Posner–Rowen–Amitsur and
Braun–Kemer–Razmyslov at statement level. No node depends on that remark.

DERIVATION
leavitt-unit-hosts-exclude-matrices-over-commutative-rings-proof
