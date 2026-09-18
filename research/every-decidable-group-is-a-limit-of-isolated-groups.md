---
rg: 2
id: every-decidable-group-is-a-limit-of-isolated-groups
kind: claim
title: Every finitely generated group with solvable word problem is a limit of isolated groups (Cornulier--Guyot--Pitsch Question 1)
requires:
  - limits-of-isolated-groups-basic-closure
  - relative-finite-discrimination-forces-solvable-word-problem
distinct_from:
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4, which asks for an isolated OVERGROUP; this asks for approximation BY isolated groups in the space of marked groups. Neither is known to imply the other.
  boone-higman-conjecture: that asks for a finitely presented simple overgroup; this is an approximation statement about the normal-subgroup structure of the input, and an embedding in a finitely presented simple group gives no nearby quotient of the input.
---

**OPEN.**

**The printed question.** Cornulier--Guyot--Pitsch, *On the isolated points in the space of
groups*, arXiv:math/0511714v2 (J. Algebra 2007), p. 10, right after their Corollary 3.7
("The class of isolated groups is not dense"), verbatim:

> "This leaves many questions open. Question 1. Is every finitely generated group with
> solvable word problem a limit of isolated groups?"

Read from the arXiv PDF on 2026-09-18 (pages 9--12). Questions 2 and 3 on p. 11 are
`every-hyperbolic-group-is-a-limit-of-isolated-groups` and
`every-fg-solvable-group-is-a-limit-of-isolated-groups`; Question 4 on p. 12 is on main as
`every-decidable-group-embeds-in-an-isolated-group`.

**Why solvable word problem.** Isolated groups have solvable word problem (CGP Corollary 3.5),
and Miller's finitely presented group whose only quotient with solvable word problem is trivial
has a neighbourhood with no isolated group (CGP Proposition 3.6). So the hypothesis cannot be
dropped.

**Known cases** (`limits-of-isolated-groups-basic-closure`): every LEF group (hence every
residually finite group), every isolated group (finitely presented simple groups such as `T` and `V`; Thompson's `F`, which is
finitely presented and monolithic since every nontrivial normal subgroup contains `F'`;
Houghton's group `H_3` by CGP §5.3, and `H_n` for `n ≥ 3` by
`fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`; Grigorchuk's finitely
presented ascending HNN extension by CGP §5.7), and finite direct products of these. The class
is strictly larger than LEF ∪ isolated (`S × Z`).

**What a counterexample needs.** A finitely presented counterexample `G` needs a finite
`F ⊂ G − {1}` such that no finitely presented quotient `G/N` with `N ∩ F = ∅` is finitely
discriminable. By `relative-finite-discrimination-forces-solvable-word-problem`, if this is to
be shown through unsolvable word problems of the quotients, the unsolvability cannot sit in one
fixed finitely generated subgroup of `G`.

**Natural test case.** `BS(2,3) = ⟨a, t | t a^2 t^{-1} = a^3⟩`: finitely presented, solvable word problem, and not
residually finite, so not LEF. In every finite quotient `a` has order prime to 6, so
`t a t^{-1}` lies in `⟨a⟩` and `[t a t^{-1}, a]` dies, while it is nontrivial in `BS(2,3)`
(Britton's lemma: `a ∉ ⟨a^2⟩`). So an isolated quotient near `BS(2,3)` must be infinite and
keep this commutator. Whether `BS(2,3)` is itself finitely discriminable (which would make it
isolated) is not checked here.
