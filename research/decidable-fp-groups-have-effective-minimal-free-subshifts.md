---
rg: 2
id: decidable-fp-groups-have-effective-minimal-free-subshifts
kind: claim
title: Every infinite finitely presented group with solvable word problem carries a nonempty effectively closed minimal free subshift
distinct_from:
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that asks for a minimal free subshift OF FINITE TYPE on some finitely presented overgroup; this asks only for an EFFECTIVELY CLOSED minimal free subshift on the group itself, with no finite-type condition.
  gjs-countable-groups-have-free-minimal-subflows: that gives a free minimal subflow of 2^G for every countable group by a non-effective construction; this asks that one such subflow be effectively closed, which Zorn or an arbitrary minimal subsystem does not provide.
  f2-groups-have-paradoxical-free-minimal-subshifts: that adds a paradox for groups with free subgroups and is not effective; this asks for effectiveness for all infinite finitely presented groups with solvable word problem.
  rf-toeplitz-subshift-has-computable-language: that is a computable minimal topologically free Toeplitz subshift over effectively residually finite groups; this needs freeness at every point and makes no residual finiteness assumption.
---

**OPEN.** Premise (M2) of route
`minimal-free-sft-via-plane-constant-minimal-simulation`.

**Statement.** Let `Λ_0` be an infinite finitely presented group with solvable
word problem. Then there are a finite alphabet `B` and a nonempty subshift
`Y ⊆ B^{Λ_0}` such that:
- `Y` is effectively closed: some recursively enumerable set of finite patterns
  defines `Y` as the set of configurations avoiding all of them;
- `Λ_0` acts minimally on `Y`;
- `Λ_0` acts freely on `Y`: `λ·y = y` for some `y ∈ Y` forces `λ = 1`.

The action is `(λ·y)(μ) = y(μλ)`.

**Equivalent forms, by hand.**
- A minimal effectively closed subshift over a finitely generated group with
  solvable word problem has decidable language.
  - *Non-occurrence is r.e.:* compactness.
  - *Occurrence is r.e.:* by minimality a pattern that occurs meets every point
    within a bounded radius, and compactness makes this a finite search. This
    is the argument of `plane-constant-minimal-sft-factors-are-effective-minimal-proof`,
    step 4, with `Φ` the identity.
- So (M2) is equivalent to the existence of a computable point `y` whose
  orbit closure is free and minimal, with a computable uniform recurrence
  function.
  - *Forward:* decidable language gives a computable point by extending
    patterns, and the recurrence radius is found by search.
  - *Backward:* a pattern on a ball `B(n)` occurs in the orbit closure iff it
    occurs in `y` within radius `f(n)`.

**Why it is a separate prerequisite.**
- *Necessary for the plane-constant design class.* By
  `plane-constant-minimal-sft-factors-are-effective-minimal`, any minimal SFT
  over `Λ_0 x Z^2` whose `Λ_0`-freeness is witnessed by a `Z^2`-invariant free
  `Λ_0`-factor produces an instance of (M2) for `Λ_0`.
- *Necessary for (P1) in weakened form.* A nonempty minimal free SFT over a
  finitely presented group `Λ` is an instance of (M2) for `Λ` itself. Jeandel
  (context only) gives solvable word problem, and every SFT is effectively
  closed. So (P1) implies that every decidable input embeds in an infinite
  finitely presented group satisfying (M2).
- *It can fail independently of (M1).* (M1) is a simulation statement that
  takes (M2)'s output as input and says nothing about existence.

**Known instances (hand arguments, not imported).**
- *`Λ_0 = Z^d`.* Take `d` Sturmian subshifts with computable irrational slopes,
  one on each coordinate of the product. The product under `Z^d` is minimal,
  because orbits of the product group are products of orbits. It is free,
  because stabilizers are products of stabilizers and an infinite minimal
  `Z`-subshift is free. It has decidable language, because Sturmian languages
  with computable slope are decidable.
- *Products.* If `G_1` and `G_2` satisfy (M2), so does `G_1 x G_2`, by the
  product subshift with the same argument.
- *Groups already carrying a minimal free SFT.* The SFT itself, which gives
  Labbé's shift over `Z^2` again (`minimal-aperiodic-wang-shift-exists`).
- *Not known here:* any infinite simple Kazhdan group, or the Clapham envelope
  of one. These are the inputs the Boone--Higman route needs
  (`boone-higman-iff-simple-kazhdan-decidable-inputs`).

## Attempts

**Attempt 1 (2026-09-17): minimal subsystem of an effective strongly aperiodic
subshift.** Aubrun--Barbieri--Thomassé (arXiv:1507.03369, context only, not
re-read) give an effectively closed strongly aperiodic subshift `Z` over every
finitely generated group with solvable word problem. Every minimal subsystem of
`Z` is free. *Dies at effectiveness.*
- A minimal subsystem is chosen by Zorn, and nothing makes it effectively closed.
- Effectively closed sets of configurations with no computable member exist,
  already for `Z`-subshifts (Cenzer--Dashti--King, context only).
- An effectively closed minimal subsystem would have a computable point by the
  equivalence above.
- The obstruction is to the method, not to (M2).

**Candidate (not attempted).** Effectivize the Gao--Jackson--Seward blueprint
construction of minimal 2-colourings.
- With solvable word problem, balls are computable finite sets, and greedy
  maximal `r`-separated sets along a shortlex enumeration are decidable.
- What must be checked is that the colouring built on these blueprints is a
  computable point with a computable recurrence modulus, and that it is
  hyperaperiodic.
