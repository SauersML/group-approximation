---
rg: 2
id: amenable-cd-two-kropholler-iff-locally-indicable
kind: claim
title: Kropholler's question in dimension 2 is equivalent to local indicability, and to every finitely generated amenable group of cd 2 having an infinite cyclic quotient; Linnell's class reaches only the elementary amenable groups
distinct_from:
  amenable-cd-two-groups-have-an-l2-rank-gap: that is the open L2-rank-gap form; this replaces the ring-theoretic input by a group-theoretic one (an infinite cyclic quotient of every finitely generated subgroup), proves both directions, and shows the gap holds for every locally indicable amenable group of cd at most 2
  amenable-cd-two-annihilator-iteration-closes-up: that shows every input implied by one zero divisor is circular; this supplies an input of a different kind, not implied by a zero divisor, that forbids all zero divisors
  amenable-left-orderable-groups-are-locally-indicable: that is Witte Morris' theorem for all amenable groups; this uses it only to translate local indicability into left-orderability and actions on the line
  strong-atiyah-passes-to-locally-indicable-extensions: that is the Jaikin-Zapirain--Lopez-Alvarez permanence theorem; this applies it to amenable groups of cd at most 2 and to their locally indicable residual
  amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical: that excludes elementary amenable normal subgroups of a counterexample; this excludes locally indicable quotients of the relevant normal subgroup and produces a counterexample with finite abelianization
---

**ESTABLISHED** (proposed; referee pending) through
`amenable-cd-two-kropholler-iff-locally-indicable-proof`, from
`strong-atiyah-passes-to-locally-indicable-extensions` (Jaikin-Zapirain–López-Álvarez,
Proposition 6.5), `amenable-cd-two-annihilator-iteration-closes-up` (item 1), `amenable-cd-two-solvable-iff-coherent-rational-group-algebra` (item 3),
`amenable-left-orderable-groups-are-locally-indicable` (Witte Morris), and, for item 5 only,
`amenable-edge-graphs-of-groups-preserve-division-ring-embeddings`.

A group is *locally indicable* (LI) if every nontrivial finitely generated subgroup maps onto `Z`.
Call a group *LI-perfect* if its only locally indicable quotient is trivial.

1. **Local indicability kills zero divisors.** Let `G` be amenable and locally indicable, of any
   cardinality. Then `Q[G]` is a domain and embeds in a division ring inside `U(G)`, so
   `rk(a) = 1` for every `0 ≠ a ∈ Q[G]`. If in addition `cd_Z G <= 2`, then `G` is solvable: it
   is `1`, `Z`, a noncyclic subgroup of `Q`, or `BS(1,m)` with `m ≠ 0`. In particular every
   finitely generated amenable LI group of cd 2 has the `L²`-rank gap with `c = 1`.
2. **Equivalence.** The following are equivalent.
   - (a) Kropholler's question holds in dimension at most 2: every amenable group of `cd_Z <= 2`
     is elementary amenable (equivalently solvable, equivalently the target
     `amenable-cd-two-groups-have-an-l2-rank-gap`).
   - (b) Every finitely generated amenable group of cd 2 has infinite abelianization.
   - (c) Every amenable group of `cd_Z <= 2` is locally indicable.
   - (d) Every amenable group of `cd_Z <= 2` is left-orderable.
   - (e) Every finitely generated amenable group of cd 2 has a nontrivial orientation-preserving
     action on `R` by homeomorphisms.
3. **Where a counterexample lives (sharpens Remark R).** Let `G` be a counterexample: amenable,
   `cd_Z G <= 2`, not solvable. Then:
   - (i) `G` contains a finitely generated counterexample `K` with **finite abelianization**. So
     `K` has no infinite cyclic quotient and no nontrivial action on the line.
   - (ii) If `ab = 0` in `Q[G]` with `a, b ≠ 0`, then `H = ⟨supp a ∪ supp b⟩` is not LI. So `H`
     contains such a `K`.
   - (iii) The *LI residual* `R(G)`, the least normal subgroup with locally indicable quotient,
     exists. It is nontrivial, LI-perfect, of cd 2, and `Q[R(G)]` is not a domain. Conversely,
     if `Q[R(G)]` were a domain, `Q[G]` would be one. So the whole obstruction sits inside
     `R(G)`, and the locally indicable quotient `G/R(G)` contributes none of it.
4. **Linnell's class is exhausted (obstruction).** Let `C` be Linnell's class: the smallest class
   containing all free groups and closed under directed unions and under extensions with
   elementary amenable quotient. An amenable group lies in `C` iff it is elementary amenable. So
   for the finitely generated subgroup `H` of Remark R, "`H ∈ C`" is equivalent to "`H` is
   solvable", i.e. to the target itself. Linnell's theorem supplies no input beyond elementary
   amenability. The locally indicable input of item 1 does go beyond it: there are finitely
   generated amenable LI groups that are not elementary amenable (left-orderable groups of
   intermediate growth, Grigorchuk–Machì; LI by Witte Morris).
5. **Splittings.** Let `K` be finitely generated with `H_1(K; Q) = 0`. Then every action of `K` on
   a tree without inversions either has a global fixed vertex or factors through a surjection
   `K ↠ D_∞`. Hence `K` has Serre's property FA unless `K = A *_C B` with `[A : C] = [B : C] = 2`.
   If `K` is a counterexample and splits in that way, then `Q[A]` or `Q[B]` is not a domain. So
   `A` or `B` (amenable, `cd <= 2`) again contains a finitely generated counterexample, by the
   amenable-edge theorem.

**Calibrations.**

- `BS(1,m)` is LI, as are all its subgroups. This is consistent with item 1.
- `Z/2 ≀ Z` has torsion, so it is not LI and item 1 does not apply. It has thin idempotents
  (`amenable-cd-two-annihilator-iteration-closes-up`, item 6).
- **Dimension 3.** (a) ⇔ (b) is special to dimension 2. The Hantzsche–Wendt (Promislow) group `P`
  is torsion-free and virtually `Z³`, so it is elementary amenable of cd 3. It has
  `H_1(P) = Z/4 ⊕ Z/4` and is not left-orderable. So the three-dimensional analogue of (b) fails
  while Kropholler's question holds there. In dimension 2 every torsion-free elementary amenable
  group is LI, because it is `1`, `Z`, a subgroup of `Q` or `BS(1,m)`.

**What this changes.** The previous lane showed that every input implied by "`Q[G]` has one zero
divisor" is circular. Item 2 gives an input of a different type: an infinite cyclic quotient of
each finitely generated subgroup. It is purely group-theoretic, involves neither `L²` nor rings,
and is not bounded by elementary amenability (item 4). Dimension-2 Kropholler is now the
statement:

> **(Q_ab)** There is no finitely generated amenable group of cohomological dimension 2 with
> finite abelianization.

By item 3(i), a minimal-looking counterexample is an infinite, torsion-free, finitely generated
amenable group `K` with `cd K = 2`, finite `H_1(K)`, trivial elementary amenable radical, and no
nontrivial action on `R`. It is not `FP_2`. By item 5, it is FA except through an index-2
amalgam. The next step is to rule out (Q_ab): for instance by showing that a finitely generated
amenable group of cd 2 has `b_1 > 0` virtually and that this suffices, or by building a
candidate. Virtual `b_1` alone does not suffice through item 1. Passing strong Atiyah through a
finite extension is open in general, so the finite-index step is where a new input is needed.
