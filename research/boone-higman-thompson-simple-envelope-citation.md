---
rg: 2
id: boone-higman-thompson-simple-envelope-citation
kind: route
title: Import Boone-Higman 1974 and Thompson 1980
target: boone-higman-thompson-simple-envelope
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Citation import.  Boone--Higman (1974) proved the equivalence with a
computably presented simple envelope; Thompson, *Embeddings into finitely
generated simple groups which preserve the word problem* (1980), added finite
generation.

Not reproved here and no Lean counterpart exists.  The statement was read
this session from the survey Belk--Bleak--Matucci--Zaremsky arXiv:2306.16356,
Theorem 3.8, verbatim — see
`research/artifacts/boone-higman-audit-2026-08-17.md` §A.1 — but the primary
papers were not.

## What is actually load-bearing

Only two adjectives: **finitely generated** and **computably presented**.
Simplicity of the envelope is used for
`proper-normal-subgroups-miss-the-normally-generating-core`, and the two
finiteness adjectives are used to feed
`chatterji-kassabov-normal-generator-embedding`, whose hypothesis is exactly
that pair.  Nothing downstream cares how the envelope is built, so a slip in
the construction would not disturb the graph, whereas weakening either
adjective would break the composition immediately.
