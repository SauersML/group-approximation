---
rg: 2
id: mapping-class-groups-are-continuous-automatic
kind: claim
root: true
title: Mapping class groups of finite-type surfaces are continuous automatic (BBCMP Question 1.16, first part)
distinct_from:
  automatic-groups-embed-in-corner-germ-extensions: that is the OPEN premise that turns a continuous automatic structure, with finitely many singular points, into a finitely presented host; this is whether mapping class groups have a continuous automatic structure at all.
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is the second part of Question 1.16, for the only open case, closed surfaces of genus at least three; this is the first part, about continuous automaticity.
  low-complexity-mapping-class-groups-are-continuous-automatic: that settles the question for punctured spheres, genus one with at most one puncture, and closed genus two; this is the question for all finite-type surfaces.
  closed-mcg-embeds-in-rational-projective-full-group: that embeds Mod(S_g) in a full group of integral projective germs on a Cantorization of PML; this asks for a normal-form boundary, which would also embed Mod(S_g) in the rational group by BBCMP Corollary 1.9.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**OPEN** in general. Settled for low complexity; see below.

## The question, verbatim

Belk--Bleak--Chatterji--Matucci--Perego, *Rational embeddings of continuous automatic
groups* (preliminary version; the PDF at
https://jimbelk.github.io/web/RationalEmbeddingsContinuousAutomaticPreliminary.pdf,
copied to `gq/src/bbcmp/`), page 7:

> **Question 1.16.** Are mapping class groups of finite-type surfaces continuous
> automatic? Do all such groups admit embeddings into finitely presented simple groups?

The sentence before it: Mosher "has proven that mapping class groups of finite type
surfaces are automatic. Note that the Boone–Higman conjecture is open for mapping class
groups of closed surfaces of genus three or greater."

This node is the first part. The second part is Boone--Higman, which is known except
for closed surfaces of genus at least three
(`punctured-surface-mcgs-satisfy-permutational-boone-higman`,
`closed-surface-mapping-class-groups-satisfy-boone-higman`).

## Definitions (BBCMP §1.1, pp. 3–4)

- A normal form `L ⊆ X^*` is *continuous* if the left action of `G` on `L` extends
  continuously to `L ∪ ∂L` (criterion: Proposition 1.3 / 2.1).
- An *automatic structure*, in their convention, is a regular `L` with `π(L) = G` such
  that each `R_x = {(α,β) : π(α) = x π(β)}` is synchronous rational.
- `G` is *continuous automatic* if some automatic structure is a continuous normal form.

## Status

- **Settled for** `S_{0,n}` (all `n`), `S_{1,0}`, `S_{1,1}` and `S_{2,0}`, by
  `low-complexity-mapping-class-groups-are-continuous-automatic`. That result goes through
  braid groups modulo their center
  (`artin-groups-mod-central-garside-power-are-continuous-automatic`) and uses BBCMP's
  commensurability invariance as printed.
- **`S_{1,2}`, conditionally.** Settled modulo one recalled Birman--Hilden identification
  with `S_{0,5}`: `twice-punctured-torus-mcg-is-continuous-automatic`.
- **Open for** every other finite-type surface. `S_{2,1}` is the first case with no
  hyperelliptic shortcut, since `ι` is not central in `Mod(S_{2,1})`. All surfaces of genus
  at least three are open, closed or punctured.

## Attempts

1. **bh-hhg, 2026-09-18.**
   - *Low complexity, closed.* Garside normal forms of the lift with small infimum,
     then capping and Birman--Hilden.
   - *Why this does not extend.* The route needs a finite-index subgroup that is a
     Garside group modulo a central subgroup. For genus at least three this lane knows
     no such identification.
   - *What the known examples use.* Normal forms on which left multiplication by each
     generator changes a bounded amount at the front and then propagates a finite-state
     carry from left to right. This is what Garside forms and Niblo--Reeves normal cube
     paths do. For Baumslag--Solitar forms it is a bounded prefix rewrite with bounded
     cancellation. It is the mechanism of these examples, not a proved necessary
     condition.
   - *Natural candidates.* Canonical flip sequences in Mosher's mapping class groupoid,
     which BBCMP Theorem 2.12 reduces to a groupoid statement for punctured surfaces.
     Also greedy train-track splitting sequences, whose infinite limits code the rational
     Cantorization of `PML` behind `closed-mcg-embeds-in-rational-projective-full-group`.
     Neither has been shown to be sequential under left multiplication.
2. **Idea only, unverified: canonical splitting as a Garside-type prefix (bh-hhg).**
   - A continuous structure needs a canonical *first move* toward the target, and it must
     change only by a bounded carry when the base point moves by one generator.
   - For train tracks, Agol's maximal splitting sequences are canonical. They split all
     branches of maximal weight at once. For pseudo-Anosov data they are eventually
     periodic, which is Agol's veering-triangulation theorem; it is recalled, not read.
   - The questions a proof would need:
     1. Is there a finite, combinatorial version of maximal splitting for group elements,
        splitting toward `g·τ_0` from a fixed track `τ_0`, that is a regular language
        after coding tracks by their finitely many combinatorial types?
     2. Is left multiplication by a generator, which changes the base track by a bounded
        move, a finite-state left-to-right carry on these sequences?
   - Neither is known to this lane. The second is where fellow-travelling results for
     splitting sequences, such as Masur--Minsky and Hamenstädt, give only coarse
     agreement, while continuity needs exact prefix agreement.
3. **bh-hhg, 2026-09-18 (fourth pass).**
   - **A test for candidates.** `continuity-of-automatic-structures-is-decidable`:
     continuity of a given automatic structure is the same as bounded lookahead of each
     left multiplier map, and it is decidable from the multiplier automata. This is the
     first test to run on Mosher's structure. Lane bh-free-51 is running its thinness and
     germ-rate tests on that structure, and those tests presuppose continuity.
   - **`S_{2,1}`.** The Birman exact sequence
     `1 → π_1(S_2) → Mod(S_{2,1}) → Mod(S_2) → 1` has a continuous automatic quotient (the
     low-complexity node). Closure of continuous automaticity under extensions, even with a
     hyperbolic kernel, is not known, and BBCMP list no such closure property. So
     `S_{2,1}` stays open. It is the natural first test case for the general methods.
   - **Genus-one calibration for the splitting idea, recalled.**
     - For `SL_2(Z)` the maximal-splitting normal forms are Farey paths, i.e. continued
       fractions.
     - Left multiplication by a fixed integer matrix acts on continued fraction expansions
       by a finite-state left-to-right transducer with bounded lookahead (Raney 1973,
       recalled, not read). So Attempt 2 is consistent in genus one.
     - The higher-genus analogue of continued fractions is Rauzy--Veech induction, or
       train-track maximal splitting. The precise missing theorem is a **Raney-type
       theorem for Rauzy--Veech codings**: `Mod(S)` acts on them by finite-state transducers
       with bounded lookahead.
