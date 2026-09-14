---
rg: 2
id: kazhdan-groups-in-sofic-permanence-closure-are-lef
kind: claim
title: Finitely generated Kazhdan groups reached from amenable and LEF groups by the sofic permanence operations are LEF
distinct_from:
  lea-permanence-closure-fp-kazhdan-groups-are-residually-finite: that is the finitely presented case, concluding residual finiteness, over a closure without iterated marked limits; this is the finitely generated case, concluding LEF, which the non-finitely-presented simple hosts need, and it allows iterated marked limits.
  gap-sofic-approximations-are-local-embeddings: that excludes sofic models through targets with a fixed-point gap, for every group; this excludes every Kazhdan group reachable by permanence operations, whatever its models.
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: that treats Kazhdan subgroups of amenable orbit full groups; this treats the closure under subgroups, unions, products, amenable extensions, graphs of groups and marked limits.
  sofic-universal-envelope-forces-non-lef-simple-kazhdan: that says a universal sofic host theorem costs a non-LEF sofic simple Kazhdan group; this says no such group comes from the permanence closure.
artifacts:
  - research/artifacts/sk-sofic-host-hamming-2026-09-13-part1.md
  - research/artifacts/sk-verify-14-2026-09-13-part6.md
---

**ESTABLISHED (unreviewed).** Let `𝒫` be the smallest class of groups that contains every amenable group and every LEF
group and is closed under:
- (O1) subgroups;
- (O2) directed unions;
- (O3) finite direct products;
- (O4) extensions `1 -> N -> G -> Q -> 1` with `N` in the class and `Q` amenable;
- (O5) fundamental groups of graphs of groups whose vertex groups are in the class, for any edge groups;
- (O6) limits in the space of marked groups.

Then every finitely generated Kazhdan subgroup of a member of `𝒫` is LEF.

**What `𝒫` contains.** Every group that the standard permanence theorems certify as sofic from amenable and LEF groups:
- amalgams and HNN extensions over amenable subgroups (Elek–Szabó, Păunescu, Dykema–Kerr–Pichot);
- graph products (Ciobanu–Holt–Rees), which are iterated amalgams;
- wreath products with amenable top group, which are directed unions of finite products extended by an amenable group;
- sofic-by-amenable extensions (Elek–Szabó);
- marked limits, and so all LEA groups.

**Consequences.**
1. **Finitely presented case.** An infinite finitely presented Kazhdan group in `𝒫` is residually finite, since
   finitely presented LEF groups are. This recovers `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite`
   (sk-fp-sofic-host), whose closure has LEA as base and no iterated limits. So any positive answer to Alekseev–Thom
   Open problem 6.1 (`fp-sofic-kazhdan-group-not-residually-finite`) lies outside `𝒫`.
2. **Simple hosts.** An infinite finitely generated simple Kazhdan group in `𝒫` is LEF. LEF passes to subgroups, so in
   `sofic-groups-embed-in-simple-kazhdan-sofic-groups` the host of a non-LEF input lies outside `𝒫`. That applies to
   the lamplighter hosts `EL_3(LC(2^Δ,F_2) ⋊ (Z/2 ≀ Δ))` for non-LEF `Δ`, which are not finitely presented, so the
   finitely presented case does not reach them.
3. **Known non-residually-finite Kazhdan groups.** Deligne's lattice (`deligne-universal-cover-lattice-is-non-rf-kazhdan`)
   and de Cornulier's finitely presented non-Hopfian Kazhdan groups are not in `𝒫`.

**Model test.**
- `SL_3(Z)` is residually finite, lies in `𝒫`, and is LEF.
- Thom's LEF non-residually-finite Kazhdan group lies in `𝒫` and is not finitely presented.
- **The Kazhdan hypothesis is needed.** `BS(2,3)` is an HNN extension of `Z` over `Z`, so it lies in `𝒫`, and it is not
  LEF.
- **Nothing is claimed for full groups.** `𝒫` omits orbit full groups of sofic relations (Elek), new sofic
  approximations, and amenable-by-sofic extensions. The artifact §4–§5 treats these.

Route: `kazhdan-groups-in-sofic-permanence-closure-are-lef-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived the induction over the closure:
- finite extensions of LEF groups, through the Kaloujnine–Krasner embedding;
- property FA for (O5);
- openness of (T) plus closedness of LEF for (O6).

The model test `BS(2,3)` shows the Kazhdan hypothesis is necessary. See `research/artifacts/sk-verify-14-2026-09-13-part6.md` §3.
