---
rg: 2
id: zaremsky-2-07-brin-thompson-nv-haagerup-or-t
kind: claim
title: "Zaremsky Problem 2.7 resolved: do the Brin-Thompson groups nV (n >= 2) have the Haagerup property, or property (T)?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 7, verbatim:
"Do the Brin–Thompson groups nV (n ≥ 2) have the Haagerup property? Or
Property (T)?"

This claim is the question. It has two parts, Haagerup and (T), and is
established only through an answer route that decides both:

- **Haagerup yes**: `zaremsky-2-07-by-haagerup` requires
  `brin-thompson-groups-nv-are-a-t-menable` and
  `brin-thompson-groups-nv-lack-property-t` (the second follows from the first,
  see `brin-thompson-nv-lack-property-t-from-a-t-menability`).
- **Haagerup no, (T) no**: `zaremsky-2-07-by-neither` requires
  `brin-thompson-2v-is-not-a-t-menable` and
  `brin-thompson-groups-nv-lack-property-t`.

Never write a `requires: []` route into this claim.

## Precise reading

`nV` is Brin's group of homeomorphisms of the Cantor cube `C^n`,
`C = {0,1}^N`, that are piecewise canonical on a finite partition into dyadic
bricks `[w_1] x ... x [w_n]`: each piece goes to a brick by the product of the
prefix replacements `w_i u ↦ w_i' u`. The list asks, for every `n >= 2`,
whether `nV` is a-T-menable and whether `nV` has Kazhdan's property (T).

Structure that settles quantifiers:

- `nV <= mV` for `n <= m` via `g ↦ g x id_{C^{m-n}}` (a product-canonical map on
  each brick `B x C^{m-n}`). The Haagerup property passes to subgroups, so
  Haagerup for all `nV` is equivalent to Haagerup for every `nV`, and failure
  for `2V` gives failure for every `nV`, `n >= 2`. A mixed answer (2V
  a-T-menable, some larger `nV` not) would need its own per-`n` claims.
- An infinite a-T-menable group does not have (T), so "Haagerup yes" answers
  both parts. Property (T) does not pass to subgroups, so the (T) part is
  per `n` in general.

Known, with sources to be quoted verbatim before any citation route:

- `V` (the case `n = 1`) has the Haagerup property: Farley, "Proper isometric
  actions of Thompson's groups on Hilbert space", IMRN 2003.
- `nV` is finitely presented and simple (Brin), of type `F_infinity`
  (Kochloukova–Martínez-Pérez–Nucinkis; Fluch–Marschler–Witzel–Zaremsky), and
  has Serre's property FA (Kato, arXiv:1504.06680).
- Fournier-Facio–Wu–Zaremsky, arXiv:2603.24687 (v of Aug 24, 2026), prove that
  abstract twisted Brin–Thompson groups have property `FW_infinity` (every
  action on a finite-dimensional CAT(0) cube complex fixes a point). Their
  Definition 2.12 and Remark 2.14 appear to cover `nV` as `SV_G` with
  `S = {1,...,n}` and trivial `G`; to be checked against the text. So any
  proper cubical action of `nV` must be on an infinite-dimensional complex, as
  for `V`.

Open status: a bounded search on 2026-09-13 (web search, the arXiv HTML of
2603.24687, the abstracts of Kato 1504.06680 and Cornulier, Annales Henri
Lebesgue 4 (2021)) found no answer to either part. The web search budget ran
out, so MathSciNet and later arXiv listings were not checked.

## Attempts

- 2026-09-13 (lane z2-07-nv-haagerup): see the answer claims for the approaches
  in progress: a commensurated set of standard charts that proves
  a-T-menability of `V` and why it fails for `n >= 2`; the Stein–Farley
  complex of `nV`, which is not CAT(0); relative-(T) subgroups as the
  obstruction side; amenable actions without finite orbits as a route to
  "no (T)".
