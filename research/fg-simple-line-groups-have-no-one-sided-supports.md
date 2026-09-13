---
rg: 2
id: fg-simple-line-groups-have-no-one-sided-supports
kind: claim
title: "A finitely generated simple group acting faithfully on the line has no nontrivial element that is the identity near an end of a component, so no micro-supported action and no finite-breakpoint PL action"
distinct_from:
  finite-cd-groups-have-no-micro-supported-line-action: that excludes micro-supported actions for groups of finite cohomological dimension; this excludes them for every finitely generated simple group of any dimension, and also rules out finite-breakpoint PL and finitely piecewise projective actions
artifacts:
  - research/artifacts/zp-left-orderable-simple-type-f-fences-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `G` be a finitely generated simple group acting faithfully on `R` by
orientation-preserving homeomorphisms, and let `C` be a component of `R \ Fix(G)`.

1. No nontrivial element of `G` is the identity on a neighbourhood of either end of `C`.
2. For every nonempty open interval `I ⊊ C`, the rigid stabilizer `G_I = {g : g fixes R \ I pointwise}` is
   trivial. So no faithful action of `G` on the line is micro-supported, whatever `cd G` is.
3. If `G` is nonabelian, it has no faithful action on `R` by PL homeomorphisms with finitely many
   breakpoints, nor by piecewise projective homeomorphisms with finitely many pieces.

**Consequences for Zaremsky Problem 1.22.**
- Every witness satisfies items 1–3.
- The rigid-stabilizer count of `finite-cd-groups-have-no-micro-supported-line-action` never separates
  simple groups by dimension. For example, the natural actions of the Hyde–Lodha simple groups (`G_ρ` of
  arXiv:1807.06478, `Q_n` of arXiv:2302.04805) are not micro-supported, although these groups have
  infinite dimension.
- Their dimension is seen by disjointly supported families whose supports are not intervals:
  `finite-cd-line-groups-bound-disjointly-supported-families`,
  `hyde-lodha-groups-contain-thompson-commutator-subgroup`.

**Model tests.**
- `F' = [F,F]` acting on `(0,1)`: simple and micro-supported, but not finitely generated.
- Thompson's `T`: finitely generated, simple, PL, but it acts on the circle, not the line.
- `Z` by translation: not simple, and every bounded rigid stabilizer is trivial anyway.

**Credit.** Hyde–Lodha, arXiv:1807.06478, §1, name germ homomorphisms at `±∞` and simplicity criteria
through compactly supported subgroups as the classical obstructions to finite generation. Items 1–2 are
the folklore form of that remark, not claimed as new.

Proof: `fg-simple-line-groups-have-no-one-sided-supports-proof`.
