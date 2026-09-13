---
rg: 2
id: fixed-marked-mf-consequences-are-uniformly-polynomial
kind: claim
title: One fixed polynomial MF consequence operator serves Kazhdan seam groups of every word-problem degree
root: true
distinct_from:
  fixed-mf-quotient-kazhdan-extensions-realize-all-word-degrees: that fixes the abstract kernel and quotient while varying word degree; this identifies the marked quotient and the entire consequence operator, with one intercept-independent polynomial algorithm.
  sturmian-seam-normal-and-mf-consequence-is-polynomial-time: that fixes computable seam intercepts; this gives one MF algorithm for all allowed intercepts, including noncomputable ones.
artifacts:
  - research/artifacts/pestov91-fixed-mf-consequences-and-hidden-degrees-2026-09-13.md
---

For the fixed-slope marked family H_beta with quotient Q x Q, let
supp(v) be the nonidentity endpoint coordinates of a word and let S(R)
be their union over the premise words. MF consequence is exactly
supp(v) contained in S(R), independently of beta. The same is true for
LEF-target consequence. A surviving endpoint map supplies a counterexample.

The exact endpoint window algorithm is polynomial in total expanded
word length, uses no intercept oracle, and decides membership in the MF
radical when there are no premises. Ambient word problems still realize
every Turing degree. This is not an identity test inside the radical.
