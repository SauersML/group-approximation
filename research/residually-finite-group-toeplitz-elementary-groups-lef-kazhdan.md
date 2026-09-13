---
rg: 2
id: residually-finite-group-toeplitz-elementary-groups-lef-kazhdan
kind: claim
title: Over any finitely generated infinite residually finite acting group, including Kazhdan groups, the Toeplitz crossed product gives infinite simple LEF Kazhdan groups EL_N/Z
distinct_from:
  toeplitz-free-group-elementary-groups-are-lef-kazhdan: that is the free-group Toeplitz family via Kerr–Nowak Theorem 5.2; this is every finitely generated infinite residually finite acting group, via a directly RF Toeplitz subshift.
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be finitely generated, infinite and residually finite, let `X_Γ` be the RF
Toeplitz subshift of `rf-toeplitz-subshifts-over-residually-finite-groups`, `q` a prime power,
`R_Γ = LC(X_Γ, F_q) ⋊ Γ` and `N >= 3`. Then:
1. `R_Γ` is a finitely generated simple ring embedding unitally and injectively in `∏_ω M_(N_n)(F_q)`;
2. `S_(Γ,N) = EL_N(R_Γ)/Z(EL_N(R_Γ))` is an infinite, finitely generated, simple group with property (T) that is
   LEF, hence sofic and hyperlinear.

Examples of acting groups: `SL_3(Z)`, `Sp_4(Z)` and other residually finite Kazhdan groups, surface groups, `Z^d`.
`Γ = Z` is the Pestov 9.1 mechanism. The Kazhdan property of `S_(Γ,N)` comes from EJZ and does not require (T) of
`Γ`; what the family adds is one explicit LEF Kazhdan simple group per residually finite acting group.

Route: `rf-group-toeplitz-elementary-groups-lef-kazhdan-proof`.

**Review (un-verify-measure, 2026-09-13): PASS. Generation, embedding, (T), simplicity mod scalars and LEF of the quotient re-derived.** See `research/artifacts/un-review-measure-2026-09-13-part5.md` §R6.
