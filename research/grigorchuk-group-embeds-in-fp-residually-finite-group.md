---
rg: 2
id: grigorchuk-group-embeds-in-fp-residually-finite-group
kind: claim
title: The first Grigorchuk group embeds in a finitely presented residually finite group
distinct_from:
  bounded-automaton-groups-embed-in-fp-automaton-groups: that asks for a finitely presented automaton overgroup of every bounded automaton group; this is the weaker necessary condition for the Grigorchuk group, with any residually finite finitely presented host.
  spine-hosts-reduce-to-fp-rf-overgroups-of-the-lamp: that shows this condition (in an automaton-embedded form) is necessary and sufficient for self-similar hosts of spine groups over the Grigorchuk group.
  grigorchuk-ascending-hnn-extension-is-finitely-presented: that is a finitely presented overgroup that is not residually finite.
  computable-tree-groups-embed-in-fp-self-similar-groups: that asks for a finitely presented self-similar host for every decidable group with a computable tree action; its instance for the Grigorchuk group implies this claim, because self-similar groups are residually finite.
---

**OPEN.** There is a finitely presented residually finite group `R` with `Γ ≤ R`.

## Constraints

- **No endomorphic conjugator.** `R` contains no element conjugating `Γ` into `St_Γ(1)`, for any action of `Γ` as
  a weakly branch group (`rf-hosts-cannot-realize-branch-substitutions`). So Lysenok's L-presentation cannot be
  realized inside `R`.
- **Not virtually torsion-free.** An infinite finitely generated torsion subgroup meets a torsion-free subgroup of
  finite index trivially, so it is finite. This rules out finite-index torsion-free overgroups such as `Aut(F_n)`,
  mapping class groups, right-angled Artin groups and linear groups over fields of characteristic zero.
- **Not linear.** Finitely generated torsion linear groups are finite (Schur).
- **The target for self-similar Boone–Higman.** The automaton-embedded form, `Γ ≤ K ≤ P` with `K` finitely
  presented and `P` a lift-presented automaton group, would make every separated automaton group over the
  Grigorchuk base Boone–Higman through self-similar hosts. This covers spine-Grigorchuk and the spine-mover group
  `M(Γ)` (`spine-hosts-reduce-to-fp-rf-overgroups-of-the-lamp`).

## Status of the literature (bounded search, settled 09-18 by bh-openq-lists)

**Not a named problem.** The following sources were searched in full text, and none asks whether the Grigorchuk
group, or any infinite finitely generated torsion group, embeds in a finitely presented residually finite group:
- the Kourovka Notebook, arXiv:1401.0300v46 (1 September 2026), whole TeX source. The nearest entry is 5.15
  (Cannonito: finitely presented residually finite groups with recursive but not primitive recursive word
  problem), which Kharlampovich–Myasnikov–Sapir answered and which is recorded on main;
- Grigorchuk, *Solved and unsolved problems around one group*, Progr. Math. 248 (2005), all numbered problems
  1.1–13.2. §4 uses the ascending HNN extension to get a finitely presented amenable overgroup, and §2 notes that
  no finitely presented branch group is known. Neither asks for a residually finite overgroup;
- Bartholdi–Grigorchuk–Šunić, *Branch groups*, arXiv:math/0510294, all `question` environments. The nearest is
  "Do there exist finitely presented branch groups?";
- 427 arXiv TeX sources from 2024–26 collected by bh-openq-lists passes 3 and 4 (`gqsrc/bh-openq/` on MSI). The only sentence about
  subgroups of finitely presented residually finite groups is Rauzy's, quoted below.

**The printed question it tests.** It is the first natural test case of a question printed by Rauzy.
- Rauzy, J. Group Theory, doi:10.1515/jgth-2020-0030, arXiv:2002.02540v2, in the closing paragraph of the
  section proving Theorem 2. Being recursively presented and effectively residually finite is necessary for being a
  subgroup of a finitely presented residually finite group, and Rauzy writes: "What we do not know yet is whether
  [this condition] … is also sufficient."
- Rauzy, J. Group Theory, doi:10.1515/jgth-2020-0029, arXiv:2002.02541, frames the same search as one for "a
  corrected Higman Embedding Theorem for residually finite groups". It asks for a finitely presented residually
  finite group with a finitely generated subgroup that lacks computable finite quotients (CFQ). It also proves
  that L-presented groups have CFQ.
- `Γ` is recursively presented and L-presented (Lysenok), so it has CFQ and is effectively residually finite.
- So if `Γ` embeds in no finitely presented residually finite group, then Rauzy's sufficiency question has a
  negative answer, even for groups with CFQ. The constraints above show where such an argument has to work: `R`
  cannot be virtually torsion-free or linear, and it cannot realize any branch substitution by conjugation.

**Priority of the constraints.** Two ingredients are in print:
- the failure of residual finiteness of Grigorchuk's ascending HNN extension, due to Sapir–Wise, JPAA 166 (2002);
- Schur's theorem on torsion linear groups.

The conjugator rigidity statements (`rf-hosts-cannot-realize-the-lysenok-substitution`,
`rf-hosts-cannot-realize-branch-substitutions`) are elementary lane proofs, and no printed source was found for
them. No priority is claimed.

## Lesson for general BH

The residually finite analogue of the Higman embedding theorem is exactly where branch groups resist. The one
mechanism that makes their L-presentations finite, conjugating the group onto an endomorphic image, is forbidden in
every residually finite host. In simple hosts it is free, because the prefix shift of `V` plays that role. So for
Boone–Higman the Grigorchuk group is easy, while for the residually finite intermediate hosts that the fp-RF
routes need (BBMZ 5.3(12), the self-similar route) it is the canonical hard input. Routes to 5.3(12) should not
pass through a finitely presented residually finite overgroup of a branch group.
