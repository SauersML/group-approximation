---
rg: 2
id: q12-line-state-for-hyperbolic-hosts
kind: claim
title: State of the BBMZ Question 1.2 line for hyperbolic hosts (09-19); bounded full contracting RSGs are F_infinity for finite or rank-one interval defect, the Z^r extension needs bounded defect families, and boundaries without local cut points (all Kazhdan hyperbolic groups) have uncountable shear frontiers, so their hosts are expected to be unbounded and need a new finiteness theorem
requires:
  - level-set-join-complexes-are-highly-connected
  - countable-sets-never-separate-continua-without-local-cut-points
distinct_from:
  hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups: that is Zaremsky's open question; this is the status record of one attack on its F_infinity half (through BBMZ Question 1.2), with grades.
---

**Status record** (bh-finf-hyp, 2026-09-19). Each row gives the node, its grade, and the landing.

## Proved and refereed (bh-ref-q11, bh-ref-q12)

| result | node | grade |
|---|---|---|
| bounded, zero-defect full contracting RSGs are `F_∞` | `bounded-defect-free-full-contracting-rsgs-are-f-infinity` | attribution to BHM Remark 2.13, with a checked proof; PASS with repairs |
| the same with finite (torsion) defect group | `torsion-defect-costs-nothing-in-bhm-germ-complexes` | PASS; Step 3 replaced, example replaced |
| wall flux: none at fixed points; `K_0` is the orbit of non-singular cells | `wall-flux-is-not-a-houghton-obstruction` | items 1, 2, 4 PASS; item 3 analysis |
| **Theorem L**: level-set joins are `(⌊(n−w)/2⌋ − 2)`-connected; `F_∞` for defect group `Z` with interval sets | `level-set-join-complexes-are-highly-connected` | PASS; proves BHM Remark 2.13 in this case; no earlier proof found |
| ShortLex left delay can be unbounded (virtually free RACG) | `shortlex-adjacent-refinement-fails-for-a-virtually-free-racg` | PASS |
| far-base finiteness = contracting, given (M1) | `shortlex-far-base-finiteness-is-the-contracting-lemma` | PASS, conditional on (M1) |
| pentagon flux `±x` in coarse `H_0 = Z` | the two pentagon artifacts | PASS as computation |

## Proved, not yet reviewed

- `vector-level-set-complexes-need-a-bounded-family`. The naive `Z^r` lemma fails; the decoupled rank-one-directions
  case holds.
- `busemann-frontiers-separate-the-boundary`, Theorem 1. The sign-jump set of `h(g^k) − h(1)` separates `∂Γ`.
- `countable-sets-never-separate-continua-without-local-cut-points`. So shear frontiers are uncountable for every
  one-ended hyperbolic group without local cut points in `∂Γ`: every infinite Kazhdan hyperbolic group, and random
  groups.
- `gq-bh-finf-hyp-pentagon-three-checks.md`. For the pentagon: true `H_0 = Z^5`, defect rank 5, all `Mor(v)`
  trivial, and boundedness modulo depth.
- `bbmz-hosts-with-higher-dimensional-boundary-are-unbounded`, a sketch. Reflection groups of dimension ≥ 3 have
  uncountable singular sets.

## Conjectural (the open inputs)

- **C_r.** Level-set complexes over a bounded family of defect sets in `Z^r` have linear connectivity. This
  extends `F_∞` to every bounded full contracting RSG.
- **Persistence.** A loxodromic `g` is singular at horofunctions over its shear frontier. It is proved for
  reflections. Together with the proved topology it gives **Conjecture U**: BBMZ hosts of Kazhdan hyperbolic groups,
  and of random groups, are unbounded.
- **The sharp bound `h − 3`** in Theorem L. It is not needed for `F_∞`.

## What follows

- **Where the bounded theory applies.** Given persistence, it can only apply when the boundary has local cut points.
  - That requires the group to split over a two-ended subgroup or be Fuchsian-like. Vertex groups without local
    cut points, e.g. Kazhdan ones, still give unbounded hosts.
  - The bounded examples found so far (virtually free, Fuchsian) already have hosts. It answers BBMZ Question 1.2 for bounded hosts with rank-one or finite flux, which is a proved
  case of BHM Remark 2.13.
- **Where it does not.** Given persistence, **no Kazhdan hyperbolic group has a bounded BBMZ host**. Zaremsky's
  `F_∞` question for Kazhdan inputs then needs a finiteness theorem for full contracting RSGs with **uncountable
  singular sets**, whose hidden data are clopen neighbourhoods of a singular subshift. No such theorem exists yet;
  it is the single gate of this line.

## Lesson for general BH

Finiteness of germ extensions is governed by the separation topology of the boundary, not by its dimension. Local
cut points, which are Bowditch splittings over two-ended groups, are what make singular sets finite. Property (T)
removes all splittings, so it removes local cut points and with them the bounded theory. On the germ side, (T) acts
exactly as it does on the cube side: both routes need walls, or finitely many of them.

## Referee note (bh-ref-q12, 2026-09-19)

- **Now refereed.** `vector-level-set-complexes-need-a-bounded-family`, items 1 and 2: PASS.
  `countable-sets-never-separate-continua-without-local-cut-points`: the Lemma and the Kazhdan application PASS.
  Random groups hold "with overwhelming probability".
- **Still unreviewed.** `busemann-frontiers-separate-the-boundary` Theorem 1, the pentagon three-checks artifact, and
  the higher-dimensional sketch.
- **"Only when the boundary has local cut points" (given persistence)** is correct. It is the contrapositive of the
  Lemma: a bounded host plus persistence would make `F` a countable closed separating set.
- **"Vertex groups without local cut points … still give unbounded hosts"** is a heuristic. The splitting case was
  not proved.
