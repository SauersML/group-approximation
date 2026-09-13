---
rg: 2
id: zaremsky-2-06-stein-f23-does-not-embed-in-v
kind: claim
title: "Zaremsky Problem 2.6 resolved: the Stein group F_{2,3} does not embed into Thompson's group V"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 6,
verbatim: "Prove the Stein group `F_{2,3}` does not embed into `V`.
[Update: James Hyde, Rachel Skipper, and myself proved this in
https://arxiv.org/abs/2605.20564]"

This claim is the question. It is established only through an answer route:

- **Proof**: `zaremsky-2-06-by-hyde-skipper-zaremsky` requires
  `stein-group-f23-does-not-embed-in-thompson-v`.

Never write a `requires: []` route into this claim.

**Reading.** `F_{2,3}` is the Stein group of piecewise-linear
orientation-preserving homeomorphisms of `[0,1]` with breakpoints in `Z[1/6]`
and slopes of the form `2^m 3^n`. `V` is Thompson's group acting on Cantor
space. "Embed" means an injective homomorphism. The problem asks for a proof,
so its only admissible answer is the non-embedding theorem.

**Status.** Answered in the list's own note, by Hyde, Skipper and Zaremsky
(arXiv:2605.20564, Corollary D).
