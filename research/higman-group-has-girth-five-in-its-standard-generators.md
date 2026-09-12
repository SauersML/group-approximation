---
rg: 2
id: higman-group-has-girth-five-in-its-standard-generators
kind: claim
title: No nonempty reduced word of length at most four in Higman's generators is trivial
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

Let `H = <a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>`. Every nonempty freely reduced word of length at most 4 in
`a^(+-1), b^(+-1), c^(+-1), d^(+-1)` is nontrivial in `H`, so the Cayley graph has girth 5.

**For automata.** Every subset of `{1, a, b, c, d}` is a Sidon memory in `H`. By
`binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective`, no binary automaton on `H` with such a memory and an
unbalanced local rule is injective. A binary injective automaton with an unbalanced rule is one form a counterexample
can take (it is strict by `unbalanced-effective-rule-certifies-strictness`); on `H` that form must use memory elements
whose quotients realize a relation of length at least 5. Counterexamples need not be binary or unbalanced, so this
filter excludes only that form.

Verified by w3-vf-nonlinear (Section 26 of its verification artifact), which also corrected the scope of this paragraph.

**ESTABLISHED 2026-09-12** by `higman-girth-five-proof`.
