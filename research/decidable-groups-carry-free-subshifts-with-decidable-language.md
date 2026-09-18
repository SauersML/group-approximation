---
rg: 2
id: decidable-groups-carry-free-subshifts-with-decidable-language
kind: claim
title: Every infinite finitely presented group with solvable word problem carries a nonempty free subshift whose language is decidable
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2), which adds minimality; (M2) implies this statement, and this statement for A implies (M2) for A * Z.
  decidable-groups-have-universal-hyperaperiodic-points: that asks for ONE computable point exhibiting all its patterns near the origin; this asks only for a subshift with decidable language, i.e. a computable dense family of points with no gluing into one point.
---

**OPEN.** Premise (D) of `free-products-with-z-inherit-m2-from-decidable-free-subshifts`.
The master route needs it only for the Clapham envelope `Λ_1` of `K × F_2`.

**Statement.** Let `A` be an infinite finitely presented group with solvable word problem.
Then there is a finite alphabet `C` and a nonempty subshift `Y ⊆ C^A` such that:
- `A` acts freely on `Y`;
- the set of finite patterns that extend to a point of `Y` is decidable.

**Equivalent forms, by hand.**
- **Computable dense family.** (D) holds iff some effectively closed free subshift has a uniformly computable sequence of
  points whose patterns exhaust its language.
  - *Forward:* greedy extension, as in Step 0 of the consumer node.
  - *Backward:* the language is r.e. through the points, and co-r.e. by compactness.
- **Decidable `Π⁰₁` class.** (D) says that some free subshift is a decidable `Π⁰₁` class of
  `C^A`.
- **Separated from effective closedness.** Effectively closed free subshifts with undecidable
  language exist already over `Z`.
  - Take the Sturmian shifts with slopes in a `Π⁰₁` class of irrationals that has no computable member.
  - A computable point would have a computable slope, by frequencies.
  - So Aubrun–Barbieri–Thomassé's theorem (every decidable f.g. group has an effectively
    closed strongly aperiodic subshift) does not give (D) as it stands. One needs a subshift
    chosen to have computable witnesses.

**Known instances.**
- Every group with (M2): a minimal effectively closed subshift has decidable language. This
  covers every infinite fp residually finite group and every infinite f.g. linear group
  (`effectively-rf-groups-have-effective-minimal-free-subshifts`).
- Every group with a computable universal hyperaperiodic point, via its orbit closure.
- Products: (D) for `A` and `B` gives (D) for `A × B`, by the product subshift.
- Free products with `Z`: (D) for `A` gives (M2), hence (D), for `A * Z`.
- *Not known here:* `St_10(R_L)`, Thompson's `V`, and Clapham envelopes of simple Kazhdan groups.

**Where it sits.**
- *Necessary for E1 at the level of `Λ`.* A minimal free SFT over `Λ` is minimal and
  effectively closed, so it has decidable language and is an instance of (D) for `Λ`. So
  E1 cannot avoid (D) for the acting group. What can be avoided is minimality and
  universality inside the envelope.
- *Chain.* The master route's E1 becomes
  (D)(`Λ_1`) ⇒ (M2)(`Λ_1 * Z`) ⇒ [MSS] ⇒ a minimal free SFT on `(Λ_1 * Z)²`.
  Here `Λ_1 * Z` is still finitely presented, decidable, non-amenable, and contains the input.
- *Why local-lemma subshifts do not settle it directly.*
  - For the Aubrun–Barbieri–Thomassé constraints (for each `s ≠ 1`, one disagreement
    `y(ag) ≠ y(asg)` inside `B(R(s))g`), a locally valid pattern need not extend.
  - A boundary cell can be the last free cell of unboundedly many straddling constraints,
    and over a finite alphabet their exclusions can exhaust `C`.
  - Strongly valid patterns do extend (Attempt 1 of
    `decidable-groups-have-universal-hyperaperiodic-points`), but they are not closed under
    subpatterns, so they are not a language.
  - What is wanted is a constraint system whose extension problem has a computable
    look-ahead: a pattern on `B(m)` extends iff it extends to `B(m + f(m))`, with `f`
    computable.

**Lesson for general BH.** After the tree removes minimality and gluing, the existence gate
E1 has an effectivity core with no dynamics in it. It asks for a free subshift of the envelope
whose extension problem is decidable. That is a "decidable `Π⁰₁` class" question, the r.e.
half of Aubrun–Barbieri–Thomassé, and it is necessary for any SFT-based route, because every
minimal free SFT is an instance of it. Attacks should look for aperiodicity constraints with
computable look-ahead, i.e. flexible or self-correcting constraint systems, not for
recurrence schemes.

**Proved at design level (2026-09-18, bh-g1-simulation; unreviewed).**
`decidable-groups-carry-flexible-free-subshifts` implies this statement, for every infinite
finitely generated group with solvable word problem, `St_10(R_L)` included.
- **The subshift.** Nested maximal separated markers carry identifiers that are locally
  distinct at each level, encoded bottom-up in four symbols. Freeness follows from those
  identifiers.
- **The computable look-ahead asked for above.** This is lemma (E) of
  `identifier-markers-give-decidable-free-subshifts`: a pattern on `B(ρ)` extends iff it
  extends validly to `B(ρ + 10r_{J(ρ)})`. Greedy marker systems have no dead ends past that
  horizon. Pockets are detected, not avoided.
- **Consequence.** Combined with `free-products-with-z-inherit-m2-from-decidable-free-subshifts`
  and `minimal-free-sft-via-m2-overgroups-and-keyed-plane-lifts`, this gives (P1) without the
  minimal self-simulation premise.
