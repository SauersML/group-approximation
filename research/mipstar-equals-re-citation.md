---
rg: 2
id: mipstar-equals-re-citation
kind: route
title: Import Ji-Natarajan-Vidick-Wright-Yuen
target: mipstar-equals-re
requires: []
artifacts:
  - research/artifacts/mipstar-re-ingestion-2026-08-20.md
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
---

Literature import.  `MIP* = RE`, Ji, Natarajan, Vidick, Wright, Yuen,
arXiv:2001.04383; read at source.  The statement transcribed in the claim is
their Theorem 12.9 (reduction from the Halting problem, with the value-1 side
witnessed by a PCC strategy) together with Corollary 12.10.

The proof is the whole paper: a gap-preserving compression procedure for normal
form verifiers (their Theorem 11.1), built from question reduction by
introspection, answer reduction by composition with a bespoke PCP whose question
distribution stays conditionally linear, oracularization, and anchored parallel
repetition; the Halting-problem protocol is then obtained by applying
compression to itself through Kleene's recursion theorem.

The anchored-repetition component is now available independently as
[[anchored-quantum-parallel-repetition]], with its exact one-copy front end in
[[anchoring-preserves-nonlocal-game-value]].  Those nodes do not purport to
reconstruct the other compression ingredients.

The consequences recorded in the claim body -- Tsirelson's problem and Connes'
Embedding Conjecture -- are the paper's Section 1.2, which attributes the
Tsirelson-to-CEC direction to Fritz and to Junge et al., and its promotion to an
equivalence to Ozawa.  Those papers are not read at source here.
