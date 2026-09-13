---
rg: 2
id: rf-higman-embedding-for-decidable-groups-fails
kind: claim
title: Some finitely generated residually finite group with solvable word problem embeds in no finitely presented residually finite group
distinct_from:
  rf-higman-embedding-for-decidable-groups: that is the universal embedding statement asked by Kharlampovich--Myasnikov--Sapir; this is its negation, witnessed by one group, imported from Rauzy's theorem.
---

**ESTABLISHED** by `rf-higman-embedding-for-decidable-groups-fails-citation` (literature import).

There is a finitely generated residually finite group with solvable word problem that is not a subgroup of any finitely presented residually finite group. So `rf-higman-embedding-for-decidable-groups` is false.

**Mechanism** (Rauzy, same source).
- *Definition.* A group `G` is effectively residually finite if an algorithm, given a word `w` on the generators with `w != e` in `G`, produces a morphism from `G` to a finite group in which `w` has nontrivial image.
- *Theorem 2.* Some finitely generated residually finite group with solvable word problem is not effectively residually finite.
- *Fact 3.* Finitely presented residually finite groups are effectively residually finite.
- *Fact 4.* Finitely generated subgroups of effectively residually finite groups are effectively residually finite.
- Theorem 1, the statement above, follows from these three.

**What this does not decide.** The obstruction is failure of effective residual finiteness. A specific decidable residually finite group that is effectively residually finite is not excluded from having a finitely presented residually finite overgroup.
- For example, `Gamma` of `cycle-transposition-lef-group-has-no-regular-tree-action` is effectively residually finite. It lies in `prod_(n>=3) Sym(Z/n)`, so a nontrivial word acts nontrivially on some coordinate, and a search finds that coordinate.
- This remark is not in Rauzy's paper.
- For the self-similar route, the live question is therefore a finitely presented residually finite overgroup of `Gamma` itself (`fp-rf-group-with-unbounded-prime-torsion`), not the universal theorem.
