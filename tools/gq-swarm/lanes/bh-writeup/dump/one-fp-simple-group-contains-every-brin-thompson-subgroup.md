---
rg: 2
id: one-fp-simple-group-contains-every-brin-thompson-subgroup
kind: claim
title: One finitely presented simple group contains every group that embeds in some Brin-Thompson group nV
distinct_from:
  common-decidable-hosts-iff-uniform-word-problem: that characterizes when a c.e. class has a common decidable host and gets a common finitely presented simple host only under Boone-Higman; this is an unconditional common host for one explicit class.
  virtually-special-groups-embed-in-brin-thompson-group-2v: that puts every virtually special group in 2V; this adds every group that needs more dimensions, such as BS(1,3) in 3V, in one host.
  twisted-brin-thompson-finite-presentation-criterion: that is Zaremsky's finite-presentation criterion for SV_G; this applies it to one explicit action and records what the resulting group contains.
---

**ESTABLISHED** (route `one-fp-simple-group-contains-every-brin-thompson-subgroup-proof`;
lane proof, not reviewed). **No priority claimed:** the host is Belk–Zaremsky's.
Their abstract (arXiv:2001.04579, read 2026-09-18) says they "produce examples of
simple groups that contain every sV and hence every right-angled Artin group,
including examples of type F∞". What this node adds is an explicit finitely
presented instance checked against Zaremsky's criterion, a closure lemma, and the
list of named classes that now sit in one host.

**Statement.**
1. Let `F` be Thompson's group acting on the set `D` of dyadic rationals in `(0,1)`.
   The twisted Brin–Thompson group `U := DV_F` is finitely presented and simple, and
   it contains a copy of `nV` for every `n ≥ 1`.
2. Consequently `U` contains a copy of every group that embeds in some `nV`. In
   particular `U` contains, all at once:
   - every virtually special group, hence every right-angled Artin group, every
     finitely generated Coxeter group, every limit group, and every hyperbolic group
     acting properly and cocompactly on a CAT(0) cube complex
     (`virtually-special-groups-embed-in-some-brin-thompson-group`, Belk–Bleak–Matucci, by citation;
     `cubulated-hyperbolic-groups-embed-in-some-brin-thompson-group`);
   - the additive group `Q` (`rationals-embed-in-brin-thompson-group-2v`, Kojima–Sheng);
   - `BS(1,3)` (`bs13-embeds-in-brin-thompson-3v`);
   - Thompson's `F`, `T`, `V`, every finite group, and `Z ≀ Z`.
3. **Closure.** Suppose `G_1, …, G_k` act faithfully on sets `S_1, …, S_k`, at least
   one infinite, each action satisfying Zaremsky's three conditions (group finitely
   presented, finitely many orbits of 2-element subsets, finitely generated point
   stabilizers). Then `G_1 × … × G_k` acting on `S_1 ⊔ … ⊔ S_k` satisfies them too.
   So `(⊔S_i)V_{ΠG_i}` is one finitely presented simple group containing every `G_i`
   and every `nV`.

**What stays open (universal forms).** A single finitely presented simple group
containing
- every hyperbolic group: `all-hyperbolic-groups-lie-in-one-fp-simple-group` (OPEN).
  It would follow from item 2 and Zaremsky Problem 2.19(a)
  (`every-hyperbolic-group-embeds-in-some-brin-thompson-group`). The known part is the
  cubulated case. Hyperbolic Kazhdan groups are the obstacle.
- every finitely generated linear group, or every `GL_n(Z)`: item 2 reaches only
  groups in some `nV`, and `every-gl-n-z-embeds-in-some-brin-thompson-group` is OPEN.
- every Baumslag–Solitar group: `BS(1,3)` is in, `BS(1,2)` in some `nV` is OPEN, and
  Bux–Llosa Isenrich–Wu's hosts are one per group.
Each of these follows from Boone–Higman by `common-decidable-hosts-iff-uniform-word-problem`
(the classes are c.e. with uniformly solvable word problem), and none is known
unconditionally.
