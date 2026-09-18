---
rg: 2
id: torelli-lower-central-quotients-satisfy-boone-higman
kind: claim
title: The Torelli lower-central quotients Mod(S_g)/T_g[c+1] (g >= 3, c >= 2), non-linear non-residually-finite Kazhdan groups, embed in finitely presented simple groups
distinct_from:
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is BH for Mod(S_g) itself (residually finite); this is BH for quotients of Mod(S_g), which are not residually finite.
  deligne-lattice-satisfies-boone-higman: that is BH for Deligne's Sp_4 lattice; these quotients contain Deligne-type lattices over Sp_2g (modulo a finite central subgroup), so a host for them also hosts such a lattice.
  torelli-lower-central-quotients-are-not-residually-finite: that proves failure of residual finiteness; this is the embedding question, which also needs the word problem.
requires:
  - torelli-lower-central-quotients-are-not-residually-finite
artifacts:
  - research/artifacts/gq-bh-bh-free-38-torelli-quotients.md
---

**OPEN.** Let `g >= 3` and `c >= 2`. The question is whether
`Q_{g,c} = Mod(S_g)/T_g[c+1]` embeds in a finitely presented simple group.
Nowak (arXiv:2609.12196, Sept 2026) proved property (T) and non-linearity;
bh-preprints flagged these groups as new hard test cases (7405a25d0).

**What is known about `Q_{g,c}`.**
- **From Nowak:** finitely generated and infinite, with property (T), and not
  linear over any field (Nowak Theorem A l.193, Theorem D l.274, Cor `cor:allfields`; read in TeX).
- **Does not virtually split over Sp_2g(Z)**, even modulo a finite subgroup
  (`torelli-lower-central-quotients-do-not-virtually-split`).
- **Not residually finite**, and modulo a finite central subgroup it contains a
  group commensurable with a Deligne lattice over `Sp_2g(Z)`
  (`torelli-lower-central-quotients-are-not-residually-finite`).

**Word problem: OPEN, and required before BH makes sense.**
- **Reduction.** Triviality of `x ∈ Mod(S_g)` in `Q_{g,c}` means membership in
  `T_g[c+1]`. That set is recursively enumerable: recognize `T_g` via the action
  on `H_1`, and enumerate products of `(c+1)`-fold commutators, using the solvable
  word problem of `Mod`.
- **Where the reduction stands.** Deciding non-membership is the open part. The
  McKinsey–Mal'cev route fails because `Q_{g,c}` is not residually finite. The
  Johnson filtration `J(c+1) ⊇ T_g[c+1]` is decidable (the action on
  `pi_1/gamma_{c+2}`). So the word problem reduces to deciding membership in
  `T_g[c+1]` inside the finitely generated nilpotent group `J(c+1)/T_g[c+1]`.
- **Heuristic, not landed.** For `c = 2` this gap should be virtually `Z` plus a
  finite group, with the `Z` detected by Morita's Casson core `d: K_g -> Q`,
  which is `Mod`-invariant and so kills `[T_g, K_g] ⊇ T_g[3]`. That would reduce
  the word problem to detecting a finite torsion part. Neither the identification
  of the gap with Hain's line nor that detection is proved here.

**Hosts ruled out.**
- **Residually finite hosts, all of them:** linear groups; groups acting
  faithfully on locally finite rooted trees
  (`self-similar-hosts-contain-only-residually-finite-groups`), which includes
  automaton and self-similar groups; and residually finite type-(A) actors.
- **Hosts that exclude Deligne-type lattices.** Any host must contain a group
  that is, modulo a finite central subgroup, commensurable with the Deligne
  lattice `S~` over `Sp_2g(Z)`. So hosts excluded for Deligne lattices, such as
  Röver–Nekrashevych groups (`deligne-lattice-embeds-in-no-rover-nekrashevych-group`,
  stated there for `Sp_4`), are expected to be excluded here too. The transfer to
  `Sp_2g` and to "commensurable modulo finite central" is not checked.

**Scope.** The case `c = 1` is different. `Q_{g,1}` is finite-by-(virtually
arithmetic `Mod/K_g`). Its residual finiteness is decided by whether Johnson's
finite 2-group `K_g/[T_g,T_g]` survives in finite quotients, which is not
addressed here.
