---
rg: 2
id: kun-thom-wreath-bernoulli-rokhlin-maximal
kind: claim
title: Uniform Bernoulli shifts over a Kun--Thom nonsofic wreath have Rokhlin entropy equal to base entropy
root: true
distinct_from:
  bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups: that is maximality on finitely generated simple Kazhdan hosts, equivalent to maximality for every group; this is maximality over one explicit surjunctive nonsofic group, which would be the first Rokhlin entropy lower bound over a nonsofic group and gives nothing for other groups.
  leavitt-unit-group-has-positive-rokhlin-entropy-action: that is positive entropy over the binary Leavitt unit group, whose surjunctivity is open; this is over a Kun--Thom wreath, whose surjunctivity is established.
  surjunctive-nonsofic-group-exists: that establishes surjunctivity of the same wreaths; this is the stronger measurable statement, which implies surjunctivity and has no known converse.
artifacts:
  - research/artifacts/rokhlin-lower-bound-mechanisms-2026-09-12.md
---

**OPEN.** Let `Γ < G` be a Kun–Thom Theorem E pair (`kun-thom-nonsofic-wreath`),
and let `W = (Z/2) wr_(G/Γ) G`. For every finite alphabet `A` with `|A| >= 2`,

    h^Rok_W(A^W, uniform product measure) = log |A|.

*Marked root because it answers a recognized question in its own right.*
- Every known lower bound for Rokhlin entropy runs through sofic entropy
  (Seward, arXiv:1501.03367, introduction), and `W` is nonsofic. A proof would
  be the first Rokhlin entropy lower bound over any nonsofic group.
- `W` is the natural test case. It is surjunctive
  (`kun-thom-nonsofic-wreaths-are-surjunctive`), so the automaton obstruction
  `strict-automaton-lowers-bernoulli-rokhlin-entropy` cannot produce a deficit.
  Its structure, a residually finite actor with locally finite lamps, is
  explicit.

It follows from `bernoulli-rokhlin-entropy-maximal-for-every-group` by
specialization ([[kun-thom-wreath-maximality-by-specialization]]). It does not
reach the binary Leavitt unit group or the tester host.

## Attempts

- **Localization.** Every deficit witness folds two of its points on a
  sofic-invisible element (`sofic-radical-localizes-bernoulli-deficit-witnesses`).
  Since `W -> G` is sofic, every witness over `W` has two points in one lamp
  coset, differing by a sofic-invisible lamp configuration. The counting proof
  covers exactly the configurations with no such fold.
- **Finite quotients cannot separate the lamps.**
  - Each finite-index normal `Δ ◁ G` gives a homomorphism
    `W -> (Z/2) wr_(G/ΓΔ) (G/Δ)`, by summing lamps over fibers.
  - If `Γ` were closed in the profinite topology of `G`, these maps would
    separate finite subsets of `W`. Then `W` would be residually finite, hence
    sofic.
  - So `Γ` is not profinitely closed, and exact finite models of every witness
    pattern do not exist (artifact §3; also noted in
    `research/artifacts/determinant-conjecture-serre-class-2026-09-11.md`).
- **Lamp-invariant factor.** A bound through the lamp-invariant factor fails
  already over `Z²` (Attempts on `every-group-has-positive-rokhlin-entropy-action`).
- **Peeling.** The surjunctivity proof for `W` transplants injective automata
  along bijections and uses no counting. No entropy analogue is known: the
  transplant is a factor map, and Rokhlin entropy is not monotone under factor
  maps over groups containing `F_2` (Bowen, arXiv:0812.2718).
- **Koopman representation.** The Koopman representation of `A^W` on the
  orthocomplement of the constants is `λ_W^⊕N`. So
  `koopman-lambda-singular-part-has-zero-rokhlin-entropy` gives no information
  here.
