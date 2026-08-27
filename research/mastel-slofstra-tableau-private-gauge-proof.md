---
rg: 2
id: mastel-slofstra-tableau-private-gauge-proof
kind: route
title: Read the incidence, word equations, and simulator marginals from the randomizing tableau
target: pzk-tableau-private-s5-gauge-normal-form
requires:
  - mastel-slofstra-private-context-augmentation-preserves-defect
artifacts:
  - research/artifacts/mastel-slofstra-tableau-compiler-audit-2026-08-23.md
---

Mastel--Slofstra Definition 8.2 names the five oblivious copies of every
source Boolean variable globally.  Definition 8.3 names every new tableau
and randomizer variable with its input-context index `i`, so two different
input contexts share none of those `S5` variables.  The three displayed
clause families are exactly `(PTN1)`.  Solving a group product for any one
missing factor proves reversibility of families two and three.  Definition
8.3 makes no distinctness or homomorphic-form assumption on the two
instructions in family one, which proves the stated exception.

The degree-five masking calculation in Definition 8.2 makes every four-share
view uniform.  Proposition 8.6 samples the randomizers uniformly, identifies
the two-point row-one law, and states that each later-row element is uniform
on `S5`.  But the isolated first gauge-update relation allows all 120
row-one values, whereas the simulator uses at most two.  This gives the
explicit witness that the canonical trace is not a universal flat-PVM
relation and completes the audit.
