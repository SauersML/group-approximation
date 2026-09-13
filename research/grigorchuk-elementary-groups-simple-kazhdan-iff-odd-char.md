---
rg: 2
id: grigorchuk-elementary-groups-simple-kazhdan-iff-odd-char
kind: claim
title: EL_n over the Grigorchuk Steinberg algebra over F_q is Kazhdan, nonsofic and non-MF for all q, and simple modulo centre iff q is odd
distinct_from:
  paradoxical-steinberg-families-kazhdan-no-mf-quotient: that lists self-similar algebras for "no MF quotient" and gets simplicity only from the Hausdorff theorem; this is the non-Hausdorff Grigorchuk case, where simplicity of the group depends on the characteristic.
  binary-leavitt-elementary-group-is-simple: that is the Leavitt algebra, simple in every characteristic; here the ring carries the same binary Leavitt family but is simple only for odd q.
artifacts:
  - research/artifacts/un-open-3-grigorchuk-characteristic-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `𝒢` be the Grigorchuk groupoid, `R_q = A_(F_q)(𝒢)` and `n ≥ 3`.
1. `R_q` is a finitely generated ring (`s_0, s_1, s_0^*, s_1^*, u_a, u_b, u_c, u_d`, plus a generator of `F_q`), so
   `EL_n(R_q)` is finitely generated with property (T).
2. For every `q`, `EL_n(R_q)` is nonsofic, and every homomorphism from it to an MF group is trivial. The ring carries a
   unital binary Leavitt family `s_x = 1_(Θ((x,e,∅),X^ω))`.
3. **`q` odd:** `S = EL_n(R_q)/Z` is an infinite, finitely generated, simple Kazhdan group with no nontrivial MF quotient.
4. **`q` even:** `EL_n(R_q)/Z` is not simple. The singular ideal `I` gives the proper noncentral normal subgroup
   `E_n(R_q, I)Z/Z`.
5. The Grigorchuk group embeds in `R_q^×` via `g ↦ u_g`.

So one groupoid yields simple Kazhdan groups with no MF quotient exactly in odd characteristic. Nonsoficity of `S`
itself (item 3) is not claimed: it would need soficity to lift through the abelian centre (Elek–Szabó), which is not
imported here.

Instance on the paradox side of `kazhdan-elementary-approximation-type-mirrors-ring-type`. Artifact §3.

Route: `grigorchuk-elementary-groups-simple-kazhdan-iff-odd-char-proof`.
