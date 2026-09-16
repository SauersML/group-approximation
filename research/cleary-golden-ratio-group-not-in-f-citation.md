---
rg: 2
id: cleary-golden-ratio-group-not-in-f-citation
kind: route
title: Import Hyde–Moore on F-obstructions, which exclude F_τ from F
target: cleary-golden-ratio-group-does-not-embed-in-thompson-f
requires: []
---

Literature import. It was recorded on 2026-09-16 by the swarm lane working on
`zaremsky-2-15b-bi-orderable-subgroups-of-v-embed-in-f`.

## Sources

1. **J. Hyde and J. T. Moore**, *Subgroups of PL_+ I which do not embed into Thompson's
   group F*, Groups Geom. Dyn. 17(2) (2023) 533–554, arXiv:2103.14911v1 (submitted
   2021-03-27). The abstract was fetched from the arXiv API on 2026-09-16:
   > "We will give a general criterion - the existence of an F-obstruction - for showing
   > that a subgroup of PL_+ I does not embed into Thompson's group F. An immediate
   > consequence is that Cleary's "golden ratio" group F_τ does not embed into F."
2. **J. Hyde, R. Skipper and M. C. B. Zaremsky**, arXiv:2605.20564v2. The TeX source was
   fetched on 2026-09-16. Its closing remark defines
   `F_\tau=F([0,1];\Z[\tau],\langle\tau\rangle)`, with `τ^2 = τ + 1` and `τ > 1`, and
   states:
   > "$F_\tau$ does not embed in $F$ \cite[Corollary~1]{hyde23}".
   The bibliography entry `hyde23` is the Hyde–Moore paper above.

## What is imported

Only the statement: `F([0,1]; Z[τ], ⟨τ⟩)` is isomorphic to no subgroup of Thompson's
group `F`.

Both sources use the same group:
- HSZ take the root `τ > 1` of `τ^2 = τ + 1`.
- The repo's `irrational-slope-f-tau-is-of-type-f-infinity` takes `(√5 − 1)/2`, which is
  its reciprocal.
- `Z[τ]` and the cyclic group `⟨τ⟩` do not depend on this choice.

## Trust boundary

The proof in Hyde–Moore (F-obstructions and the dichotomy theorem for subgroups of
`PL_+ I`) was NOT read. The import rests on the paper's own abstract and the restatement
by Hyde–Skipper–Zaremsky, who cite it as Corollary 1.

Referee (2026-09-16) checks:
- The arXiv TeX source of 2103.14911 was fetched. Its first corollary is
  `\begin{cor} \label{Ftau} Cleary's group $F_\tau$ does not embed into $F$.`, so it is
  Corollary 1.
- The paper's examples section defines `F_τ` with `τ > 1` and `τ^2 = τ + 1`.
- Crossref confirms the journal record Groups Geom. Dyn. 17(2) (2023) 533–554,
  DOI 10.4171/ggd/708.
