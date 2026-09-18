---
rg: 2
id: ct-p-z-has-a-finite-class-transposition-presentation
kind: claim
title: For finite P, CT_P(Z) has an explicit finite presentation by class transpositions of bounded modulus, obtained by truncating the transposition presentation; a literature-free route to Kourovka 17.61
distinct_from:
  ct-p-z-is-a-one-vertex-k-graph-full-group: that gets finite presentation (indeed F_infinity) from Li's theorem on k-graph full groups; this asks for an explicit finite presentation with an elementary proof, suitable for formalization.
  class-transposition-relations-present-ct-p-z: that is the infinite presentation; this is its finite truncation.
artifacts:
  - research/artifacts/gq-bh-pal-kourovka61-presentation.md
---

**OPEN.**

## Statement

For every finite set `P` of odd primes there are bounds `K ≤ K'` in `N_{P'}` with the following
property. `CT_P(Z)` is presented by:
- the class transpositions `t(A,B)` whose two moduli are at most `K`;
- the relations (R1)–(R3) of `class-transposition-presentation-has-central-kernel` in which
  every box that occurs, including children, has modulus at most `K'`.

## Why it is the Lean-suitable target

The positive answer to Kourovka 17.61 on main (`ct-p-z-is-a-one-vertex-k-graph-full-group`)
rests on Li's `F_∞` theorem, Matui's simplicity theorem and the Farsi–Kumjian–Pask–Sims
homology computation. A formalization needs an explicit presentation and an elementary
completeness proof instead. The finite truncation can only work once the infinite presentation
is known to present the group, so `class-transposition-relations-present-ct-p-z` is the first
step.

## A second literature route (read at source)

Martínez-Pérez, Matucci and Nucinkis, arXiv 1609.07058, "Presentations of generalisations of
Thompson's group V". TeX is in the swarm scratchpad `gq/src/mmn/`.
- **The framework** (Definition `sigmadef`). A free Cantor algebra `U_r(Σ)` on colours of
  arbitrary arities `n_i`. The laws `Σ_2^{i,i'}` identify, through a bijection `φ`, the
  length-two expansions "colour `i` then colour `f(j)`" with "colour `i'` then colour `f'(j)`".
  `V_r(Σ)` is its automorphism group (Definition `groups`).
- **Complete** (Definition `complete`): every `Σ_2^{i,i'}` is non-empty, with `f ≡ i'` and
  `f' ≡ i`.
- **Theorem `fp`.** For valid, bounded and complete `U_r(Σ)`, `V_r(Σ)` has an explicit finite
  presentation, obtained by truncating their infinite presentation (their equation
  `infinitepresentation`). The simple connectivity of a truncated Stein complex comes from their
  Section 3 and Bestvina–Brady Morse theory.
- **Instance, checked in the artifact.** Take colours `p ∈ P'` of arity `p`, with laws
  identifying "`p`-child `j`, then `q`-child `l`" with "`q`-child `j'`, then `p`-child `l'`"
  whenever `j + p l ≡ j' + q l' (mod pq)`. These laws hold in the Boolean algebra of boxes, and
  they are complete.
- **Not checked.** Whether that `U_1(Σ_P)` is valid and bounded in their sense (defined in
  Martínez-Pérez–Nucinkis 1105.0189, not read). Also whether `V_1(Σ_P) = CT_P(Z)`, which needs the
  box algebra to be the free algebra `U_1(Σ_P)` and class transpositions to generate its
  automorphism group.
- **Priority consequence.** If both checks pass, finite presentation of `CT_P(Z)` also follows from
  this 2016 theorem via the identification. The Kourovka answer's novelty is then the
  identification alone. Recorded so the Palomar surface does not overclaim.

## Attempts

1. **bh-pal-kourovka61, 09-18.** Built the infinite presentation, and proved its kernel central
   and the extension perfect (`class-transposition-presentation-has-central-kernel`). Recorded
   the MMN route above. No truncation bound was proved. Reasons:
   - it needs the infinite presentation first, which is OPEN;
   - a Bleak–Quick-style "all deep relations are conjugates of shallow ones" argument needs the
     conjugation relations for deep boxes to follow from shallow ones, which is not done.
