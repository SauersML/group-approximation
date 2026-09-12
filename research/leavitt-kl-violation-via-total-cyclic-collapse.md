---
rg: 2
id: leavitt-kl-violation-via-total-cyclic-collapse
kind: route
title: Normally generate the degree-m kernel, and every Leavitt coefficient dies at once
target: kl-violating-equation-over-leavitt-unit-group
requires: [leavitt-degree-kernel-normally-generated-by-one-word, kl-simple-failure-leaves-only-the-cyclic-quotient]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Let `w` be as in the first prerequisite: `deg_t(w) = m >= 1` and
`<<w>>_{R^x * <t>} = N_m`.  By part (b) of the second prerequisite, applied
to the nontrivial group `R^x`,

    (R^x * <t>)/<<w>>  =  (R^x * <t>)/N_m  =  C_m ,

so every element of `R^x` dies while `deg_t(w) = m != 0`.  That is a
nonsingular equation over `R^x` with no solution in any overgroup containing
`R^x`, which is the target.

## Why this route is worth having

It replaces "find an equation that kills *some* coefficient" — an existential
over both the word and the element — with a single identity between two
subgroups.  The sharpening is free: part (b) of the collapse claim needs only
`R^x != 1`, not simplicity, which this repository does not know for `R^x`.
The external audit states the equivalence only for simple coefficient groups;
this direction is the half that survives without that hypothesis, which is
what makes it usable here.

## What it does not change

The difficulty, and the logical scope.  Per
`kl-violation-refutes-hyperlinearity-route`, evidence that `R^x` violates
Kervaire--Laudenbach bears on `non-hyperlinear-group` only and says nothing
about Pestov's Question 3.4; and per the target's own body, no
Kervaire--Laudenbach-violating equation is known over any group, so this
remains a falsification instrument rather than a plausible attack.
