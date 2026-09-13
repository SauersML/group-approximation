---
rg: 2
id: every-decidable-group-embeds-in-an-isolated-group
kind: claim
title: Every finitely generated group with solvable word problem embeds in an isolated group (Cornulier--Guyot--Pitsch Question 4)
distinct_from:
  boone-higman-conjecture: that asks for a finitely presented simple overgroup and implies this, since finitely presented simple groups are isolated; this asks only for a finitely presented, finitely discriminable overgroup, which CGP print as a separate, weaker question.
  permutational-boone-higman-conjecture: that asks for a finitely presented overgroup with a type (A) action; this asks for a finitely presented, finitely discriminable overgroup and does not mention actions.
  decidable-groups-embed-in-outer-extensions-of-fp-simple-groups: that is a specific sufficient condition, an overgroup that is an outer extension of a finitely presented simple group; this is the printed question itself.
  linear-and-metabelian-groups-embed-in-isolated-groups: that is this question answered on the finitely generated quasi-linear groups; this is the question for all groups with solvable word problem.
---

**OPEN.**

**The printed question.** Cornulier--Guyot--Pitsch, *On the isolated points
in the space of groups*, arXiv:math/0511714, read on 2026-09-13 from the TeX
source on MSI (`/scratch.global/sauer354/bh-isolated/math_0511714.tex`). It is
the fourth `question` environment, lines 828–834, verbatim:

> "Does every finitely generated group with solvable word problem embed into
> an isolated group?"
>
> "Note that the stronger well-known question whether every finitely
> generated group with solvable word problem embeds in a finitely presented
> simple group is open."

**Terms.** A group is isolated iff it is finitely presentable and finitely
discriminable (CGP Proposition, lines 554–557). Finite discrimination is the
existence of a finite `F ⊂ G − {1}` meeting every non-trivial normal subgroup
(Proposition--Definition, lines 519–533).

**Why solvable word problem is necessary.** CGP (line 705): "An isolated group
has solvable word problem." A finitely generated subgroup of a group with
solvable word problem has solvable word problem, so the hypothesis cannot be
dropped.

**Known cases.** `linear-and-metabelian-groups-embed-in-isolated-groups`:
every finitely generated group linear over a finite product of fields,
including every finitely generated linear or metabelian group. More generally,
every group on main that is known to embed in a finitely presented simple
group.

## Attempts

1. **Permutational wreath monoliths.**
   - **Sources.** CGP Proposition `prop wreath_nocentre`: `W ≀_X G` is finitely
     discriminable when `X = G/H` is faithful and transitive and `W ≠ 1` is
     finitely discriminable with trivial centre. Their Theorem
     `thm wreathfinpres`, due to Cornulier (arXiv:math/0509090, Theorem in §1,
     TeX lines 147–157): for `W ≠ 1`, `W ≀_X G` is finitely presented iff `W`
     and `G` are finitely presented, `H` is finitely generated, and `G` has
     finitely many orbits on `X x X`.
   - **Reduction.** So an isolated wreath monolith over a faithful transitive
     `X`, with `W` finitely presented and centreless, is exactly a type (A)
     action of `G` (`type-a-action-gives-boone-higman-for-subgroups`: finitely
     many orbits on ordered pairs is equivalent to finitely many orbits on
     two-element subsets). An input placed in `G` already lies in the
     permutational Boone--Higman class. A finitely generated input placed in
     the base `W^(X)` lies in a finite product `W^n`.
   - **Verdict.** Killed as a new route: it reduces to
     `permutational-boone-higman-conjecture`, or to subgroups of products of
     one finitely presented group.
2. **Split outer actions on one fixed simple group.**
   - **Setup.** Let `Q ≤ Aut(S)` be finitely generated with `Q ∩ Inn(S) = 1`.
   - **Why it fails.** `q = 1` in `Q` iff `q` fixes the finitely many generator
     images of `S`, so the word problem of `Q` reduces to that of `S` with a
     recursive time bound depending only on `S`. By
     `complexity-bounded-host-classes-are-not-universal`, no single `S` serves
     every input this way. This is a hand argument, first noted in
     `research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md`, approach 2.
   - **Verdict.** Killed for a fixed `S`; `S` must depend on the input.
3. **Non-split outer extensions of a fixed simple group.**
   - **Setup.** Let `1 → S → I → Q → 1` with `Q → Out(S)` injective.
   - **Original remark (superseded; see Status).** Here `q = 1` iff some lift of
     `q` acts on `S` by an inner automorphism. That is a search for a conjugator
     in `S`, with no time bound depending only on `S`. So one fixed `S` is not
     ruled out by `complexity-bounded-host-classes-are-not-universal`: the
     overgroup `I` varies with the input, and so does its word-problem
     complexity. This is a hand remark.
   - **Status.** Refuted on 2026-09-13 by
     `outer-extension-word-problem-is-kernel-bounded` (lane
     solve-bh-outer-ext).
     - The innerness search above decides triviality in the quotient `Q`, but
       the input must sit in `I`.
     - Since `C_I(S) = 1`, `I` embeds in `Aut(S)`, and the word problem of `I`
       reduces to that of `S` after one exponential substitution.
     - So one fixed `S`, split or not, is excluded by
       `complexity-bounded-host-classes-are-not-universal`.
     - The outer-extension route therefore needs unboundedly complex simple
       kernels, as the conjecture does
       (`complex-fp-simple-groups-from-outer-extensions`).
