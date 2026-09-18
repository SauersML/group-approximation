---
rg: 2
id: contracting-rsgs-embed-in-fp-simple-groups
kind: claim
title: Full contracting rational similarity groups embed in finitely presented simple groups, and every RSG with finite nucleus sits in a full one
distinct_from:
  hyperbolic-groups-embed-in-contracting-rsgs: that imports BBMZ's embedding of hyperbolic groups into full contracting RSGs (their Theorem E); this imports the host side, that full contracting RSGs embed in finitely presented simple groups, plus the classification of full RSGs by their nuclei.
  hyperbolic-groups-satisfy-boone-higman: that is the end result for hyperbolic groups; this is the general host theorem, usable for any group that lands in a contracting RSG.
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

**ESTABLISHED (literature import).** Source: J. Belk, C. Bleak, F. Matucci,
M. C. B. Zaremsky, *Hyperbolic groups satisfy the Boone--Higman conjecture*,
arXiv:2309.06224 (v3). Read from the arXiv TeX source (fetched via MSI; local copy
`$GQ/src/bh-free-03/bbmz2-2309.06224.tex`). Line numbers refer to that file.

Let `Sigma_Gamma` be a subshift of finite type (infinite directed paths in a finite
graph `Gamma`) with an irreducible core, let `E` be a nonempty clopen subset, and let
`R_{Gamma,E}` be the group of rational homeomorphisms of `E` (finitely many local
actions). Then:

1. (Prop. `RSGsAndV`, l. 642) `V_{Gamma,E}` is an RSG, "as is any subgroup of
   `R_{Gamma,E}` that contains `V_{Gamma,E}`".
2. (Prop. `NucleusHasProperties`, l. 735) the nucleus of any RSG is a nucleus of
   injections.
3. (Thm `RSGCharacterization`, l. 770) for a nucleus of injections `N`,
   `G = {f in R_{Gamma,E} : Nuc_f ⊆ N}` "is a full RSG with nucleus `N`".
4. (Thm `fin_pres`, l. 840) "Every full, contracting RSG is finitely presented."
5. (Prop. `contr_to_simple`, l. 1752) "Every full, contracting RSG embeds into a
   finitely presented simple group." The host is a twisted Brin--Thompson group
   `SV_G` (proof at l. 1833, via Zaremsky's Theorem 4.2 of *A taste of twisted
   Brin--Thompson groups*).

Here "contracting" (Def. `contracting`, l. 694) means `Sigma_Gamma` has an irreducible
core and the nucleus `Nuc_G` (the union of the sets of local actions occurring
infinitely often, over `g in G`) is finite; "full" means closed under homeomorphisms
that locally agree with the group (Def. `full`, l. 556).

**Consequence used downstream.** If `G_0 <= R_{Gamma,E}` contains `V_{Gamma,E}` and
has finite nucleus `N`, then by 1–3 the group `G_N` is a full contracting RSG
containing `G_0` and every homeomorphism of `E` that locally agrees with `G_0`, and by
5 it embeds in a finitely presented simple group.

Citation route: `contracting-rsgs-embed-in-fp-simple-groups-citation`.
