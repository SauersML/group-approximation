---
rg: 2
id: resolvent-elementary-group-is-fp
kind: claim
refuted_by:
  - resolvent-elementary-groups-are-not-fp
title: For some l and N >= 5, the elementary group E_N(R_l) of the finitely presented residually finite resolvent ring is finitely presented
distinct_from:
  rf-resolvent-elementary-group-is-fp: that asks the same for E_N(R̄_l) over the smaller model ring, whose presentation is not the eight relations; this is over the finitely presented ring R_l itself, now known to be residually finite.
  resolvent-steinberg-rf-residual-is-finitely-normally-generated: that allows killing only the finite residual of St_N(R_l); this asks that the whole kernel K_2(N,R_l) be finitely normally generated.
---

**OPEN.** There are a prime `l` and `N >= 5` such that `E_N(R_l)` is finitely
presented. Equivalently, since `St_N(R_l)` is finitely presented
(`steinberg-groups-of-fp-rings-are-fp-in-rank-five`), the kernel
`K_2(N, R_l)` of `St_N(R_l) -> E_N(R_l)` is the normal closure of a finite set.

**Use.** `E_N(R_l) <= GL_N(R_l)` is residually finite because `R_l` is
(`resolvent-presentation-ring-is-residually-finite`), and it contains `Z_(l)` as
`e_12(θ(Z_(l)))`. So this claim gives `z-localized-embeds-in-fp-rf-group`, by route
`z-localized-fp-rf-via-fp-resolvent-elementary-group-over-r-l`.

**Risk.** The corner tame symbols of Attempt 1 of
`resolvent-steinberg-rf-residual-is-finitely-normally-generated` would, if infinitely many
are nontrivial and independent and `K_2(N, R_l)` is central, make `K_2(N, R_l)` an
infinitely generated central subgroup and refute this claim.

## Attempts

None yet (2026-09-18, lane gq-infinite-primes).

- **Refuted (2026-09-18, lane gq-k2-q).** `resolvent-elementary-groups-are-not-fp`: for every `l` and `N >= 3`,
  `E_N(R_l)` is not finitely presented. The corner symbols are independent in `K_2(R_l)`, as detected in
  `R_l/J = D ⋉ M_Z^fin(Z_(l))` (`resolvent-ring-corner-symbols-survive-in-k2`). The symbol lemma then applies, with no
  centrality hypothesis on `K_2(N, R_l)`.
