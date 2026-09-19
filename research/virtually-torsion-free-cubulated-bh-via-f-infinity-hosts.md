---
rg: 2
id: virtually-torsion-free-cubulated-bh-via-f-infinity-hosts
kind: route
title: BBCMP Question 1.15 follows from the F_infinity simple hosts of free cocompact cubulations, since F_infinity groups are finitely presented and the torsion-free finite-index subgroup of a cubulated group is again a free cocompact cubulation
target: virtually-torsion-free-cubulated-groups-satisfy-boone-higman
requires:
  - torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups
---

**Internally refereed, through its input.** Let `G` be virtually torsion-free, and let `G`
act properly and cocompactly on a CAT(0) cube complex `X`.
1. **The torsion-free subgroup.** Let `G_0 ≤ G` be torsion-free of finite index. It acts
   properly and cocompactly on `X`, and freely on vertices, because vertex stabilizers are
   finite.
2. **The host.** Item 2 of `torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups`
   (normal core, Krasner–Kaloujnine, `S ≀ Q ≤ S`) embeds `G` in a simple group `S` of type
   `F_∞`.
3. **Finite presentation.** Type `F_∞` implies type `F_2`, i.e. finitely presented. So `G`
   embeds in a finitely presented simple group, which answers BBCMP Question 1.15. ∎

## Lesson for general BH

A named question about a class often reduces to one host theorem plus closure of the host
class under finite-index overgroups. Having the wreath closure `S ≀ Q ≤ S` built into the host
(through a prefix code in the Cuntz factor) makes "virtually" free.
