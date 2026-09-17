---
rg: 2
id: ring-elementary-bh-hosts-are-kazhdan
kind: claim
title: Every quotient of an elementary group of rank at least three over a finitely generated ring is Kazhdan, so every ring-host Boone--Higman host has property (T)
distinct_from:
  elementary-groups-over-fg-rings-have-property-t: that is the imported Ershov--Jaikin-Zapirain theorem for EL_n(R) itself; this adds permanence under quotients and abstract isomorphism, and applies it to the specific finitely presented simple hosts that the three ring routes to Boone--Higman produce.
  rank-twelve-leavitt-simple-non-mf: that proves (T) for the single binary Leavitt host EL_12(L); this covers the whole families E_n(B ⊗ L), (B ⊗ L)^x and PEL_4(L) over arbitrary finitely presented coefficient algebras.
  kazhdan-boone-higman-conjecture: that is the open universal statement; this is an established permanence lemma which turns the ring-host routes to Boone--Higman into routes to that conjecture with the same open premises.
  ck-finite-bi-index-hole-is-kazhdan-boone-higman: that identifies the double-coset hole with Kazhdan Boone--Higman; this shows that Kazhdan Boone--Higman costs nothing beyond Boone--Higman along the ring-host routes.
artifacts:
  - research/artifacts/ring-hosts-are-kazhdan-2026-09-17.md
---

**ESTABLISHED** through `ring-elementary-bh-hosts-are-kazhdan-proof`.
Elementary given the imported Ershov--Jaikin-Zapirain theorem. Not
independently reviewed.

## Statement

Let `R` be a finitely generated associative unital ring and `n >= 3`.

1. Every quotient group of `EL_n(R)`, and every group isomorphic to one, has
   property (T).
2. **Elementary Leavitt hosts.** If `B` is a finitely presented unital
   `F_2`-algebra and `L = L_(F_2)(1,2)`, then `E_n(B ⊗ L)` has (T) for every
   `n >= 3`. This is the host of `leavitt-tensor-elementary-host-criterion`
   and of the route `infinite-simple-input-bh-via-elementary-leavitt-hosts`.
3. **Unit-group Leavitt hosts.** If moreover `B` is central simple and
   `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`, then the unit group `(B ⊗ L)^x` has (T).
   This is the host of `boone-higman-via-central-simple-leavitt-tensor-host`.
4. **Projective hosts.** If `L` is a finitely generated unital ring, then
   `PEL_4(L) = EL_4(L)/Z(EL_4(L))` has (T). This is the host of
   `boone-higman-via-projective-ring-host`.

## Consequence

Each of the three ring-host routes to `boone-higman-conjecture` is, with the
same open premise and no extra one, a route to
`kazhdan-boone-higman-conjecture`, and so, through
`ck-finite-bi-index-hole-via-kazhdan-boone-higman`, to the free-core reading
of `ck-envelope-simple-core-has-finite-bi-index`. The routes are
`kazhdan-boone-higman-via-central-simple-leavitt-tensor-host`,
`kazhdan-boone-higman-via-elementary-leavitt-hosts` and
`kazhdan-boone-higman-via-projective-ring-host`.

Kazhdan Boone--Higman is strictly harder than Boone--Higman only along the
routes whose hosts come from Thompson-like groups: twisted Brin--Thompson
groups, Rover--Nekrashevych groups and shell or full groups of Cantor
actions. For those hosts (T) is open, and it is open even for `nV`
(`brin-thompson-groups-nv-lack-property-t`).

DERIVATION
ring-elementary-bh-hosts-are-kazhdan-proof
