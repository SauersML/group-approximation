---
rg: 2
id: elementary-group-trace-amenable-iff-ring-rf-proof
kind: route
title: "Kazhdan collapse plus levels: finite quotients of EL_n(R) are exactly finite quotient rings of R"
target: elementary-group-trace-amenable-iff-ring-residually-finite
requires:
  - kazhdan-trace-amenable-iff-qd-iff-fd-limit
  - elementary-groups-over-fg-rings-have-property-t
  - elementary-root-kernel-equals-level
---

G = EL_n(R) is Kazhdan (`elementary-groups-over-fg-rings-have-property-t`), so
`kazhdan-trace-amenable-iff-qd-iff-fd-limit` makes the first three conditions equivalent.

- **R RF ⟹ G RF.** For g ≠ 1, some entry r of g − 1 is nonzero. Choose a finite-index ideal I ∌ r. The
  reduction G → GL_n(R/I) lands in a finite group, and ḡ − 1 has the entry r̄ ≠ 0, so ḡ ≠ 1.
- **G RF ⟹ R RF.** For r ≠ 0, choose a finite-index normal N ∌ e_12(r). By
  `elementary-root-kernel-equals-level`, {a : e_ij(a) ∈ N} = I := lev(N) for each i ≠ j. I is additive; for
  a ∈ I and b ∈ R, [e_12(a), e_23(b)] = e_13(ab) ∈ N and [e_12(b), e_23(a)] = e_13(ba) ∈ N, so I is a
  two-sided ideal. The additive map a ↦ e_12(a)N has kernel I, so R/I embeds in the finite group G/N, and
  r ∉ I.

**Corollary A.** A simple ring has no proper finite-index ideal, and an infinite one is not RF.
**Corollary B.** 2m[1] ≤ m[1] passes to R/I by base change, and for a finite ring Q it forces
|Q|^{2m} ≤ |Q|^m, so Q = 0. For a full defect: in a finite ring t̄s̄ = 1 gives s̄t̄ = 1, so 1 − s̄t̄ = 0
generates Q, and Q = 0.
**Corollary C.** The embedding is `simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md` §3.2. Limits
of normalized matrix ranks satisfy the Sylvester axioms, and {rk = 0} is a proper two-sided ideal.

Full text: `research/artifacts/un-traces-2026-09-13-part1.md` §3.
