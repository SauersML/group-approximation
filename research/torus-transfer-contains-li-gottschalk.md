---
rg: 2
id: torus-transfer-contains-li-gottschalk
kind: claim
title: The torus-to-finite transfer contains Gottschalk's conjecture for every locally indicable group, and every transfer mechanism that stays among torus-surjunctive hosts proves it
distinct_from:
  torus-surjunctivity-implies-finite-alphabet-surjunctivity: that is the transfer C3 for every group (OPEN); this proves that C3 implies surjunctivity of every locally indicable group with no torus hypothesis left, and that mechanisms landing in the established torus-surjunctive class are proofs of that.
  locally-indicable-groups-are-torus-surjunctive: that proves the torus side at locally indicable hosts; this uses it to show that the torus hypothesis of C3 carries no information there.
  sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group: that is a dichotomy about soficity of locally indicable finite presentations; this says C3 must prove surjunctivity of exactly those groups, including at a nonsofic one if branch (b) holds.
  gottschalk-surjunctivity-conjecture: that is surjunctivity of every group; this is the implication from C3 to surjunctivity of the locally indicable class and of the other established torus-surjunctive hosts.
artifacts:
  - research/artifacts/torus-transfer-li-hosts-2026-09-19.md
---

Let `𝒞` be the class of groups that are torus-surjunctive at every dimension, and C3 the node
`torus-surjunctivity-implies-finite-alphabet-surjunctivity`.

**Claim.**
1. **(Localization.)** For each `G in 𝒞`, C3 at `G` is equivalent to the surjunctivity of `G`.
2. **(Containment.)** If C3 holds, then every locally indicable group is surjunctive. So is every
   group with an elementary-admissible normal subgroup whose quotient is residually finite or
   locally residually prime-power, including every virtually locally indicable group.
3. **(Mechanism kill.)** Consider a rule that sends each strict pair over a locally indicable
   group `G` to a strict torus automaton over a host `H`. If `H` always lies in `𝒞`, the rule
   proves that no locally indicable group carries a strict pair. Such hosts include:
   - `G`, `G x Z^k` and `Z^k wr G`;
   - locally indicable extensions of `G`;
   - `G x F` with `F` finite, and finite-index overgroups of `G`.

   So a mechanism must build a host outside the established part of `𝒞`. Its output degree
   matrix must be supported on a finitely generated subgroup that is neither locally indicable
   nor residually prime-power. That subgroup must contain either non-prime-power torsion not
   absorbed by admissible kernels, or a finitely generated perfect subgroup. Hosts such as
   `F wr G` with `|F|` not a prime power, or hosts containing `Alt_fin(N)`, are not known to
   lie in `𝒞`.

**Consequence.** With `compiler-rope-is-locally-indicable` (proposed), C3 implies that every
compiler rope `R_e` is surjunctive. Soficity of `R_e` is OPEN
(`compiler-positive-rope-is-not-sofic`). If branch (b) of
`sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group` holds, C3 therefore contains
Gottschalk's conjecture at a finitely presented nonsofic group.

The step C3 of `gottschalk-via-torus-alphabet-degree-transfer` is therefore not a transfer at
LI hosts: there it is the target restricted to a class not known to be sofic. At those hosts
the rank-1 linear shadows agree in every characteristic (artifact Section 5). So the
characteristic gap is not the source of difficulty there.

**ESTABLISHED 2026-09-19** by [[torus-transfer-contains-li-gottschalk-proof]].
The Section 5 remark is supplementary and is not part of the claim.
