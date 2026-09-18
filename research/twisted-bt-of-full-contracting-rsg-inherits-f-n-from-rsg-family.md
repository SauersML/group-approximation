---
rg: 2
id: twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family
kind: claim
title: The twisted Brin-Thompson group of a full contracting RSG is of type F_n as soon as the full RSGs with the same nucleus on clopen subsets are, and only if the RSG itself is; so a yes to BBMZ Question 1.2 would give every hyperbolic group an undistorted embedding in a simple group of type F_infinity
distinct_from:
  hyperbolic-groups-undistortedly-embed-in-fp-simple-groups: that proves the undistortion and records that the F_infinity half for SV_Γ comes down to BBMZ quest:F_infty; this proves the reduction, including the finite-set stabilizers that Belk-Zaremsky's criterion also needs.
  contracting-rover-nekrashevych-groups-are-f-infinity: that is the open F_infinity question for Röver-Nekrashevych groups, a special case of BBMZ quest:F_infty; this is a consequence of a positive answer to the general question and does not settle it.
  virtually-compact-special-groups-undistorted-in-2v: that settles both refinements unconditionally for cubulated hyperbolic groups, through 2V; this is conditional and covers every hyperbolic group, Kazhdan ones included.
---

**ESTABLISHED as a conditional reduction** by `rsg-finite-set-stabilizers-are-iterated-ascending-hnn-proof`
(lane proof, not independently reviewed; no priority claimed). **The hypothesis is BBMZ Question 1.2
(`quest:F_infty`), which is OPEN.** BBMZ, arXiv:2309.06224, TeX l.221–222: "Do full, contracting RSGs
have type F∞? Even for Röver–Nekrashevych groups of contracting self-similar groups, this remains open."
So nothing here is an unconditional F_∞ statement.

## Statement

Let `Γ <= R_{Γ,E}` be a full contracting RSG with nucleus `Nuc`, and `S` the `Γ`-orbit of a rational
point. Let `𝓕(Γ)` be the full RSGs `{f ∈ R_{Γ,E'} : Nuc_f ⊆ Nuc}` for nonempty clopen `E' ⊆ E` (BBMZ
`thrm:RSGCharacterization`). All of them are full and contracting, and `Γ ∈ 𝓕(Γ)`. Let `n ∈ N ∪ {∞}`.

1. **Stabilizers.** For every finite set `S'` of rational points, `Stab_Γ(S')` has a finite-index
   subgroup that is an `|S'|`-fold iterated ascending HNN extension of some `Fix_Γ(U) ∈ 𝓕(Γ)`. So if
   every member of `𝓕(Γ)` is of type F_n, then so is `Stab_Γ(S')`.
2. **Sufficient.** If every member of `𝓕(Γ)` is of type F_n, then `SV_Γ` is of type F_n.
3. **Necessary.** If `SV_Γ` is of type F_n, then `Γ` is of type F_n.
4. **Consequence.** Suppose BBMZ `quest:F_infty` has a positive answer. Then every hyperbolic group `G`
   quasi-isometrically embeds in the simple group `SV_Γ`, with `Γ = [[G*Z | ∂_h(G*Z)]]`, and that group
   is of type F_∞. This would settle Zaremsky's hyperbolic item (arXiv:2201.00711, TeX l.495–497)
   completely, Kazhdan hyperbolic groups included. The undistortion is
   `hyperbolic-groups-undistortedly-embed-in-fp-simple-groups`.

Item 3 shows that no condition on stabilizers or orbits can bypass `quest:F_infty` for this host. For
the BBMZ host, the F_∞ half for a given hyperbolic group needs `Γ` itself to be F_∞.

## What was checked and what is not available

- **BBMZ Theorem 3.1.** This is `thrm:fin_pres`, TeX l.840, and it gives finite presentability only.
- **Skipper–Zaremsky.** Their arXiv:1709.06524 asks whether `V_d(G)` is of type F_∞ for every finitely
  generated contracting `G`. On main this is `contracting-rover-nekrashevych-groups-are-f-infinity`, which
  is OPEN; only the polynomial-activity case is settled there, by a lane proof. This is the Röver–Nekrashevych
  special case of `quest:F_infty`, so it cannot supply F_∞ for the horofunction full groups either.
- **Literature.** Two web searches on 09-18 found F_∞ results only for Röver–Nekrashevych groups of
  bounded automata groups, and nothing for full contracting RSGs in general or for horofunction full
  groups of hyperbolic groups.

## Lesson for general BH

In the full-group route to Boone–Higman, the stabilizer clauses of the Zaremsky and Belk–Zaremsky
criteria cost nothing extra. Suppose a full group has virtually cyclic germs at the points of an orbit and
contains cone-contracting elements. Then every finite-set stabilizer is, up to finite index, an iterated
ascending HNN extension of the same kind of full group on a smaller clopen set. So the finiteness type of
the simple envelope `SV` is governed by one question: the finiteness type of the full-group family
itself. The proof uses only fullness, virtually cyclic germs and cone maps. It applies verbatim to any
full-group host with these features, not just RSGs, and makes "find an F_n full group containing `G`" the
whole problem.
