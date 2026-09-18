---
rg: 2
id: every-fg-solvable-group-is-a-limit-of-isolated-groups
kind: claim
title: Every finitely generated solvable group is a limit of isolated groups (Cornulier--Guyot--Pitsch Question 3; they expect a negative answer)
requires:
  - limits-of-isolated-groups-basic-closure
  - relative-finite-discrimination-forces-solvable-word-problem
distinct_from:
  every-decidable-group-is-a-limit-of-isolated-groups: that is Question 1, restricted to solvable word problem; this has no word-problem hypothesis but restricts to solvable groups.
  fp-metabelian-groups-satisfy-boone-higman: that embeds metabelian groups in finitely presented simple groups; this is about approximating solvable groups by isolated groups.
---

**OPEN.**

**The printed question.** Cornulier--Guyot--Pitsch, arXiv:math/0511714v2, p. 11, verbatim:

> "Question 3. Is every finitely generated solvable group a limit of isolated groups?"
>
> "Note that there exist finitely presented solvable groups with unsolvable word problem
> [Kar81]; this suggests a negative answer."

**Known positive cases** (`limits-of-isolated-groups-basic-closure`): every residually finite
finitely generated solvable group, hence every finitely generated metabelian group (P. Hall,
cited by CGP), every polycyclic group, every residually finite soluble minimax group; the
isolated solvable groups (CGP Proposition 10: a 3-solvable non-Hopfian isolated group from
Abels' groups); and finite products of these. A counterexample must be non-LEF.

**On the suggested negative answer.** For a finitely presented solvable `G` with unsolvable
word problem (Kharlampovich), a negative answer at `G` means: some finite `F ⊂ G − {1}` such
that no finitely presented quotient `G/N` with `N ∩ F = ∅` is finitely discriminable. The naive
mechanism, in which a fixed finitely generated subgroup with unsolvable word problem embeds in
every such quotient, is impossible: `relative-finite-discrimination-forces-solvable-word-problem`
gives, for every finite `F`, a nearby finitely presented quotient `G/⟨⟨k⟩⟩` in which a
nontrivial `k` of that subgroup dies. A counterexample through word problems must therefore
make the nearby quotients undecidable through subgroups that depend on the quotient, or must
defeat finite discriminability by other means (for example infinitely many independent
minimal normal subgroups, or none). For finitely generated but not finitely presented `G` the
nearby groups need not be quotients of `G`, and neither reduction applies.

**Test cases.** Kharlampovich's finitely presented solvable groups with unsolvable word problem;
finitely generated solvable groups with a central quasicyclic subgroup `Z(p^∞)` (P. Hall's
centre-by-metabelian constructions), which are not residually finite because a divisible central
subgroup dies in every finite quotient.
