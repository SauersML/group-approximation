---
rg: 2
id: low-complexity-mapping-class-groups-are-continuous-automatic
kind: claim
title: The mapping class groups of punctured spheres, of the torus and once-punctured torus, and of the closed genus-two surface are continuous automatic
distinct_from:
  mapping-class-groups-are-continuous-automatic: that is BBCMP Question 1.16 for all finite-type surfaces; this answers it for the surfaces whose mapping class groups are commensurable with a braid group modulo its center or with SL_2(Z).
  artin-groups-mod-central-garside-power-are-continuous-automatic: that is the Garside lemma for Artin groups modulo a central Garside power; this transfers it to mapping class groups by capping and Birman--Hilden.
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is Boone--Higman for closed genus at least three, open; this is continuous automaticity in genus at most two, where Boone--Higman is already known through BFFHZ.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). Proof:
`low-complexity-mcg-continuous-automatic-proof`.

## Statement

The mapping class group is continuous automatic, in the sense of
Belk--Bleak--Chatterji--Matucci--Perego (BBCMP, preliminary version, §1.1), for each of:
- the sphere with `n` punctures, `S_{0,n}`, for every `n ≥ 0`;
- the torus `S_{1,0}` and the once-punctured torus `S_{1,1}`;
- the closed surface of genus two, `S_{2,0}`.

## Scope

- **Dependence.** It relies on BBCMP Proposition 1.4(2), that continuous automaticity is
  a commensurability invariant. That result is stated in their introduction. Its proof
  is not in the preliminary text read (§§1–2.5, pp. 1–16). Theorem 2.12 there proves
  the passage to isotropy groups of connected groupoids, which covers finite-index
  subgroups. This node uses Proposition 1.4(2) as printed, in both directions.
- **Not covered.** Every other finite-type surface, for example `S_{1,2}` and all
  surfaces of genus at least three. For these, BBCMP Question 1.16 remains open
  (`mapping-class-groups-are-continuous-automatic`).
- **Boone--Higman is not new here.** For all surfaces listed above it is already known
  (`punctured-surface-mcgs-satisfy-permutational-boone-higman`).
