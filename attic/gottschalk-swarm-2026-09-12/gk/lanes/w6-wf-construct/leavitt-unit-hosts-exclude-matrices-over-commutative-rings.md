---
rg: 2
id: leavitt-unit-hosts-exclude-matrices-over-commutative-rings
kind: claim
title: Leavitt unit groups over prime fields have no nontrivial hosts inside matrices over commutative rings
distinct_from:
  leavitt-unit-hosts-need-nilpotents-of-unbounded-index: that uses unipotence of p-power elements and covers rings with bounded nilpotence index; this uses residual finiteness of finitely generated linear groups and covers matrices over commutative rings whose nilpotents have any index.
artifacts:
  - research/artifacts/weakly-finite-hosts-construction-census-2026-09-12.md
---

**ESTABLISHED** on paper, importing Malcev's theorem at statement level. Verification is requested from
w4-vf-linear-b.

Let `C` be a nonzero commutative ring and `n >= 1`.
1. Every homomorphism `L_(F_2)(1,2)^x -> GL_n(C)` is trivial.
2. If `C` has characteristic 3, no homomorphism `G_3 = L_(F_3)(1,2)^x -> GL_n(C)` sends `z = -1` to `-1`. This part
   assumes every normal subgroup of `G_3` lies in `{±1}` or equals `G_3`.

**Why.**
- **Finite generation.** Both groups are finitely generated.
- **Malcev.** Finitely generated subgroups of `GL_n(C)` are residually finite, so the image is a residually finite
  quotient.
- **Quotients.** The only quotients of these groups are the group itself, `G_3/{±1}` in the ternary case, and `1`.
  The nontrivial ones are infinite and have no proper finite-index normal subgroup, so the image is trivial.

**Scope.** This covers `GL_n(C)` for non-reduced `C` with nilpotents of any index, which
`leavitt-unit-hosts-need-nilpotents-of-unbounded-index` does not reach. It also covers `∏_i M_n(C_i)` at fixed `n`.
The artifact's Remark B.2 extends it to every PI host, conditional on the Posner–Rowen–Amitsur and
Braun–Kemer–Razmyslov theorems at statement level; no node depends on that remark.
