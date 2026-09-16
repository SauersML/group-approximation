---
rg: 2
id: wreath-z-by-z2-does-not-embed-in-thompson-v-citation
kind: route
title: Import Corwin's theorem that Z wr Z^2 is not a subgroup of V
target: wreath-z-by-z2-does-not-embed-in-thompson-v
requires: []
---

Literature import. It was recorded on 2026-09-16 by the swarm lane working on
`zaremsky-2-15b-bi-orderable-subgroups-of-v-embed-in-f`.

## Sources

1. **Nathan Corwin**, *Embedding and Nonembedding Results for R. Thompson's Group V and
   Related Groups*, PhD thesis, University of Nebraska–Lincoln, 2013 (adviser Mark
   Brittenham), https://digitalcommons.unl.edu/mathstudent/48. The landing-page abstract
   was fetched on 2026-09-16 and says:
   > "This thesis obtains some further understanding of the structure of V by showing the
   > nonexistence of the wreath product Z wr Z^2 as a subgroup of V, proving a conjecture
   > of Bleak and Salazar-Diaz. This result is achieved primarily by studying the
   > topological dynamics occurring when V acts on the Cantor Set. We then show the same
   > result for one particular generalization of V, the Higman-Thompson Groups G_{n,r}."
2. **J. Burillo, S. Cleary and C. E. Röver**, *Obstructions for subgroups of Thompson's
   group V*, arXiv:1402.3860v2. The TeX source (`vdistort.tex`) was fetched on
   2026-09-16. It states, citing Bleak–Salazar-Díaz (Trans. Amer. Math. Soc. 365 (2013)
   5967–5997) and Corwin's thesis:
   > "Neither the free product $\Z*\Z^2$ nor the standard restricted wreath product
   > $\Z\wr\Z^2$ with $\Z^2$ as top group are subgroups of $V$."

## What is imported

Only the statement: the standard restricted wreath product `Z ≀ Z^2`, with base
`⊕_{Z^2} Z` and top group `Z^2` acting by translation, is isomorphic to no subgroup of
Thompson's group `V`.

## Trust boundary

- The thesis PDF (digitalcommons `viewcontent.cgi?article=1049&context=mathstudent`)
  returned HTTP 403 behind a Cloudflare challenge on 2026-09-16, so the proof was NOT read.
- The import rests on the thesis abstract plus an independent restatement as a theorem in
  a survey by three specialists.
- The in-repo evidence is consistent with the theorem. Part 3 of
  `research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part3.md` kills
  wandering-lamp and two-cone models. Part 2 of the same series proves the `F` case. But
  it does not reprove the `V` statement.
