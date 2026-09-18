---
rg: 2
id: z-localized-embeds-in-fp-kazhdan-steinberg-group
kind: claim
artifacts:
  - research/artifacts/gq-referee-b-z-localized-embeds-in-fp-kazhdan-steinberg-group.md
title: For every prime l and N >= 4, Z_(l) embeds in the finitely presented Kazhdan group St_N(R_l) of the eight-relator resolvent ring
distinct_from:
  z-localized-embeds-in-fp-rf-group: that asks for a finitely presented residually finite overgroup; this gives a finitely presented overgroup whose residual finiteness is open (resolvent-steinberg-group-is-residually-finite).
  leavitt-pairs-embed-sl-n-q-in-steinberg-groups: that embeds SL_n(Q) in Steinberg groups over rings with a Leavitt pair, which are never residually finite; this embeds Z_(l) in the Steinberg group of a ring with no Leavitt pair in its residually finite model.
  sl-n-z-localized-embeds-in-fg-rf-elementary-group: that embeds SL_n(Z_(l)) in the finitely generated residually finite groups E_N(R̄_l); this lifts the Z_(l) part to the finitely presented St_N(R_l).
---

**ESTABLISHED** through `z-localized-embeds-in-fp-kazhdan-steinberg-group-proof`.
The lane assembly passed citation review (gq-referee-b, artifact above). The finite
presentation and property (T) are imported.

**Statement.** Let `l` be a prime, `R_l` the finitely presented ring of
`resolvent-ring-presentation-is-not-faithful-on-r-bar`, and `N >= 4`.
1. There is a unital ring homomorphism `θ : Z_(l) -> e R_l e` whose composite with
   `R_l -> R̄_l` is the injective `θ` of `rf-resolvent-ring-has-z-localized-corner`.
2. `c -> x_12(θ(c))` is an injective homomorphism `(Z_(l),+) -> St_N(R_l)`.
3. `St_N(R_l)` is finitely presented and has property (T)
   (`steinberg-finite-presentation-and-kazhdan-theorem`: Krstić--McCool Theorem 3,
   and Ershov--Jaikin-Zapirain).
   **Rank.** Every use downstream works with any `N >= 4`, so `N >= 5` may be assumed.
   For `N >= 5` finite presentation also follows, with no literature input, from
   `steinberg-groups-of-fp-rings-are-fp-in-rank-five`. At `N = 4` it rests on
   Krstić--McCool Theorem 3, read only in secondary sources. Property (T) is imported in
   every rank.
**Position.** This proves the finitely presented half of
`z-localized-embeds-in-fp-rf-group`. What remains is residual finiteness:
`resolvent-steinberg-group-is-residually-finite` would finish it, through route
`z-localized-fp-rf-via-rf-resolvent-steinberg-group`.
