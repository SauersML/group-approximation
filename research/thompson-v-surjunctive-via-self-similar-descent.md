---
rg: 2
id: thompson-v-surjunctive-via-self-similar-descent
kind: route
title: Prove V surjunctive by a descent on strict pairs through cylinder copies of V
target: thompson-v-surjunctive
requires:
  - v-self-similar-descent-simplifies-strict-pairs
---

**Dead.** The plan: rewrite a minimal strict pair into a simpler one through `V_U ~= V` on
disjoint clopens. The rewrites change nothing (`v-self-similar-rewrites-preserve-strict-pairs`),
and the prerequisite is refuted.

This is the approach `thompson-v-surjunctive` lists under "What is left", an induction on the
automaton using `V_U ~= V`, in the form built from rewrites of the pair itself.
