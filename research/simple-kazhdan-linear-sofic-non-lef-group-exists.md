---
rg: 2
id: simple-kazhdan-linear-sofic-non-lef-group-exists
kind: claim
title: Some infinite finitely generated simple Kazhdan group is linear sofic over a finite field and not LEF
distinct_from:
  fp-simple-kazhdan-linear-sofic-group-exists: that asks for a finitely presented group and is open; this is the finitely generated version, where a non-residually-finite amenable subgroup certifies non-LEF instead of finite presentation.
  free-minimal-subshift-elementary-groups-are-sofic: that asks for soficity over Z^2 SFTs; this certifies linear soficity and non-LEF over an Abels--Pruefer subflow and says nothing about soficity.
  rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group: that is the ring-level middle rung; this adds simplicity of the group modulo centre and linear soficity.
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that gives simple Kazhdan linear sofic groups over Z^d subshifts with no non-LEF certificate for d >= 2; this certifies non-LEF.
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `p` be a prime, `Γ_p` the Abels–Prüfer group of
`abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, `X ⊆ 2^(Γ_p)` a free minimal subflow, `q` a prime power, and
`R = LC(X, F_q) ⋊ Γ_p`. For every `N >= 3`, `S_N = EL_N(R)/Z(EL_N(R))` is:
- infinite, finitely generated and simple;
- Kazhdan;
- `F_q`-linear sofic;
- not LEF.

**Mechanism.**
- Følner rank models, since `Γ_p` is amenable.
- The adjoint theorem turns them into a linear sofic `S_N`.
- The acting group `Γ_p` sits inside `S_N` by Whitehead's lemma. It is finitely presented and not residually finite, hence
  not LEF.

**For the UN program.** This is the measure side without towers. The ring has rank models but no exact matricial models,
and the group lies strictly between the Pestov end (LEF) and the paradox end (no MF quotient). Soficity, hyperlinearity and
MF of `S_N` are open.

Route: `simple-kazhdan-linear-sofic-non-lef-via-abels-prufer-subflow`.
