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
  - torelli-lower-central-quotients-have-solvable-word-problem
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

- **Solvable word problem**, for every `c >= 1`
  (`torelli-lower-central-quotients-have-solvable-word-problem`). The proof is
  the extension lemma: `N_{g,c}` is finitely generated nilpotent, and `Sp_2g(Z)`
  is finitely presented with solvable word problem. So for `c >= 2` these are
  genuine Boone–Higman inputs. The first version of this node (cf691c5e9) called
  the word problem open; that was too cautious and is superseded.

**Hosts ruled out.** `Q_{g,c}` is itself an infinite Kazhdan group that is not
residually finite. So every exclusion of the form "Kazhdan subgroups of X are
residually finite, or finite" applies to it directly. No transfer through Deligne
lattices is needed.
- **Every residually finite host:**
  - linear groups;
  - groups acting faithfully on locally finite rooted trees
    (`self-similar-hosts-contain-only-residually-finite-groups`), which includes
    automaton and self-similar groups;
  - residually finite type-(A) actors.
- **Every Röver–Nekrashevych group** `V_d(H)` or `V_(d,r)(H)`, for any
  self-similar `H`, and all their subgroups
  (`kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`). This is the same
  argument that excludes Deligne's lattice
  (`deligne-lattice-embeds-in-no-rover-nekrashevych-group-proof`, §3), and it
  applies verbatim.
- **Every Cremona group** `Bir(P^n_k)`, over any field
  (`kazhdan-subgroups-of-cremona-groups-are-residually-finite`).
- **Thompson's V**, whose Kazhdan subgroups are finite
  (`thompson-v-has-haagerup-property`).
- **Full groups of essentially free measure-preserving actions of amenable
  groups** (`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`).
- **Open for this input:** `nV` with `n >= 2`. It is excluded if any one of three
  open statements holds:
  - `kazhdan-subgroups-of-brin-thompson-groups-are-finite`;
  - the weaker `kazhdan-subgroups-of-brin-thompson-groups-have-finite-center`;
  - `heisenberg-group-embeds-in-no-brin-thompson-group`, since `Q_{g,c}` contains
    `H_3(Z)` (`deligne-lattices-and-torelli-quotients-contain-heisenberg-groups`).

**Deligne-type sublattices.** Modulo a finite central subgroup, `Q_{g,c}`
contains a group commensurable with the Deligne lattice over a congruence
subgroup of `Sp_2g(Z)`
(`torelli-lower-central-quotients-are-not-residually-finite`). So a host for
`Q_{g,c}` also hosts such a lattice up to a finite central subgroup. This is a
second, independent reason the exclusions above hold. Nothing further transfers
from `deligne-lattice-satisfies-boone-higman`, because that node's own
exclusions are exactly the Kazhdan non-residually-finite ones listed here.

**Scope: `c = 1`.**
- **The structure.** By Johnson, `B = K_g/[T_g,T_g]` is a finite 2-group, the
  torsion of `H_1(T_g)`. So `1 -> B -> Q_{g,1} -> Mod(S_g)/K_g -> 1`. Morita
  (cited, not read here) embeds `Mod/K_g` in `(1/2)Λ³H ⋊ Sp_2g(Z)`, so it is
  linear and residually finite.
- **The criterion** (elementary, lane proof). A finite-by-(residually finite)
  group is residually finite exactly when some finite-index subgroup meets the
  finite kernel trivially. For `Q_{g,1}` that means `[T_g,T_g]` is closed in the
  profinite topology of `Mod(S_g)`, or equivalently that finite quotients of
  `Mod(S_g)` detect every Birman–Craggs–Johnson class in `B`.
- **Status.** Not decided here. Finite central extensions of `Sp_2g(Z)` by
  2-groups can fail to be residually finite (the Deligne covers of degree
  `2^k`, `k >= 2`, have finite residual `<z^2>`), so a positive answer is not
  automatic.
