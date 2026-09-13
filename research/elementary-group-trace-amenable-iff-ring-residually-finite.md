---
rg: 2
id: elementary-group-trace-amenable-iff-ring-residually-finite
kind: claim
title: "For a finitely generated ring R and n >= 3, the canonical trace of EL_n(R) is amenable iff quasidiagonal iff R is a residually finite ring"
distinct_from:
  binary-leavitt-unit-group-fails-factorization-property: that proves failure of (F) for one nonsofic Leavitt unit group through nonsoficity; this characterizes (F) for every elementary group by a ring condition, and needs no nonsoficity.
  simple-kazhdan-lef-group-c-star-fails-llp: that derives LLP failure for the Pestov group from Ozawa's remark; this places both the Pestov and the Leavitt groups on the same non-amenable side of an exact ring criterion.
artifacts:
  - research/artifacts/un-traces-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let R be a finitely generated unital associative ring, n ≥ 3, and
G = EL_n(R). The following are equivalent:
- τ_G on C*_max(G) is amenable (G has Kirchberg's factorization property);
- τ_G is quasidiagonal;
- G is residually finite;
- R is residually finite: every r ≠ 0 avoids some two-sided ideal of finite index.

**Corollary A.** If R is finitely generated, simple and infinite, τ_{EL_n(R)} is not amenable. This covers
both calibrating rings of the UN program, L_{F_q}(1,2) and LC(X,F_q)⋊Z.

**Corollary B (paradox passes to quotients).** If 2m[1] ≤ m[1] in V(R) for some m ≥ 1, in particular if
ts = 1 and R(1−st)R = R, then every nonzero quotient ring of R is infinite, so τ_{EL_n(R)} is not amenable.

**Corollary C (a candidate refuted).** "τ_{EL_n(R)} is QD iff R admits a faithful Sylvester rank function
that is a limit of matrix ranks" is false. The Pestov ring embeds unitally in ∏_ω M_{N_k}(F_q), so
rk(x) = lim_ω rank Ψ_k(x)/N_k is a faithful rank function (its kernel is a proper ideal of a simple ring).
Yet τ_{EL_3} is not QD by Corollary A. The canonical QD trace is blind to paradox versus measure: the
separating trace invariant is the corona trace (`corona-traces-separate-paradox-from-measure-for-el-n`).

Proof route: `elementary-group-trace-amenable-iff-ring-rf-proof`.
