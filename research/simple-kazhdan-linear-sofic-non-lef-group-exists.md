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
  - research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed; the non-LEF step was repaired 2026-09-13 by lane sk-subgroups).**

Let:
- `p` be a prime and `Γ_p` the Abels–Prüfer group of `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`;
- `X ⊆ 2^(Γ_p)` a free minimal subflow;
- `q` a prime power, and `R = LC(X, F_q) ⋊ Γ_p`.

For every `N >= 3`, `S_N = EL_N(R)/Z(EL_N(R))` is:
- infinite, finitely generated and simple;
- Kazhdan;
- `F_q`-linear sofic.

For `N >= 4`, `EL_N(R)` is not LEF. For `q = 2` the centre is trivial, so `S_N = EL_N(R)` is not LEF.
This scope is narrower than the earlier every-`q`, every-`N >= 3` non-LEF assertion. That assertion rested on the
diagonal map `diag(u_γ, u_γ^(-1), 1)`, which is not a homomorphism on the nonabelian `Γ_p`
(`whitehead-diagonal-map-is-not-multiplicative`).

**Mechanism.**
- **Linear soficity.** `Γ_p` is amenable, so there are Følner rank models; the adjoint theorem turns them into a linear
  sofic `S_N`.
- **Not LEF (`N >= 4`).**
  - A LEF `EL_N(R)` would make `R` a LEF ring (`lef-elementary-groups-force-lef-rings`).
  - `R` is countable and simple, so it would then be exactly matricial (`simple-lef-rings-are-exactly-matricial`).
  - So `R^×` would be LEF (`exactly-matricial-rings-have-lef-general-linear-groups`).
  - But `R^× ⊇ {u_γ} ≅ Γ_p`, which is finitely presented and not residually finite, hence not LEF.
- **Centre over `F_2`.** Central elements of `EL_N(R)` are scalars from `Z(R)^× = F_2^× = {1}`.

**For the UN program.** This is the measure side without towers. The ring has rank models but no exact matricial models,
and the group lies strictly between the Pestov end (LEF) and the paradox end (no MF quotient). Soficity, hyperlinearity and
MF of `S_N` are open.

**Routes.**
- Current: `simple-kazhdan-linear-sofic-non-lef-via-lef-converse`.
- Invalidated: `simple-kazhdan-linear-sofic-non-lef-via-abels-prufer-subflow`, whose step 6 used the diagonal map as a
  homomorphism.

**Review (un-verify-3, 2026-09-13): PASS of the earlier route.** Re-derived: `Γ_p` is not RF, because `c_p` dies in every finite quotient (regular representations are finite-dimensional unitary), hence not LEF by finite presentation. The subflow ring is finitely generated and simple with scalar centre and (T). Faithful Følner rank models plus the reviewed adjoint theorem give `F_q`-linear soficity. `research/artifacts/un-review3-2026-09-13-part3.md` §5. Its non-LEF step, "the Whitehead embedding of `Γ_p`", used the non-multiplicative map and is superseded. The repaired route is queued with sk-verify-3.

## Attempts
- **Rank 3.** Is `EL_3(R)` not LEF? Three routes to a certificate fail or stall:
  - the LEF converse needs `N >= 4`;
  - the diagonal embedding of `Γ_p` is not a homomorphism;
  - `diag(u_γ, 1, 1)` embeds `[Γ_p, Γ_p]` in `EL_3(R)`, but certifies nothing without a proof that this derived subgroup is not LEF.
  So rank 3 is open.
- **`q > 2`.** `EL_N(R)` is not LEF for `N >= 4`. Whether its finite central quotient `S_N` is LEF is not settled here.
