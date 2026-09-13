---
rg: 2
id: baumslag-gersten-embeds-in-no-rover-nekrashevych-group
kind: claim
title: Every homomorphism from the Baumslag--Gersten group to an almost-automorphism group of a regular rooted forest kills a, so BG embeds in no Rover--Nekrashevych group and in no Higman--Thompson group
distinct_from:
  deligne-lattice-embeds-in-no-rover-nekrashevych-group: that excludes a non-residually-finite Kazhdan group through property (T); this excludes the Baumslag--Gersten group, which surjects onto Z and has neither (T) nor FW, through an equicontinuity argument.
  baumslag-gersten-group-is-neither-linear-nor-self-similar: that excludes self-similar groups of tree automorphisms, which are residually finite; this excludes the Rover--Nekrashevych groups over them, which contain V and are not residually finite.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that is the general theorem on Kazhdan subgroups of V_d(H); BG has no (T), and this excludes it by a different argument.
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

**ESTABLISHED** (elementary; no novelty claimed).

**Statement.** Let `BG = < a, t | b a b^-1 = a^2 >`, where `b = t a t^-1`.
Let `A_{d,r}` be the almost-automorphism group of `X_{d,r}`, as in
`almost-automorphism-conjugate-to-proper-power-is-equicontinuous`.
- Every homomorphism `φ : BG → A_{d,r}` has `φ(a) = 1`, so it factors through
  `BG/<<a>> = Z`.
- Hence `BG` embeds in none of these groups:
  - any Röver--Nekrashevych group `V_{d,r}(G)`, for any self-similar
    `G ≤ Aut(T_d)`, contracting or not;
  - any Higman--Thompson group `V_{d,r}`, and in particular `V`, `T` or `F`.

**Sharpness.** The stable letter `t` is essential.
- `BS(1,2) = < a, b >` acts faithfully and self-similarly on the ternary tree
  by `x ↦ x+1` and `x ↦ 2x` on `Z_3`
  (`baumslag-gersten-odometer-fixed-point-proof`, Item 3).
- So `BS(1,2)` lies in `V_3(G)` for that `G`.

**Not covered.**
- Brin--Thompson groups `nV`.
- Twisted Brin--Thompson groups `SV_G`.
- Rational similarity groups.
- Eventually-similar groups over shifts of finite type with several cone
  types, or with non-isometric local groupoids.

In every Cantor-space host, the image of `a` must fail to be equicontinuous
(`baumslag-gersten-equicontinuous-generator-acts-trivially`).

The proof is `baumslag-gersten-rn-obstruction-via-equicontinuity`.
