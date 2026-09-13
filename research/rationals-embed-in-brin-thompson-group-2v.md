---
rg: 2
id: rationals-embed-in-brin-thompson-group-2v
kind: claim
title: The additive group Q embeds in the Brin-Thompson group 2V, hence in nV for every n >= 2
distinct_from:
  zaremsky-2-19e-rationals-embed-in-2v-resolved: that claim is Zaremsky's question 2.19(e); this claim is its affirmative answer.
---

**ESTABLISHED** by `rationals-embed-in-brin-thompson-group-2v-proof`
(unreviewed by a verifier lane as of 2026-09-13).

The additive group `Q` of the rationals is isomorphic to a subgroup of the
Brin–Thompson group `2V`. Since `2V` embeds in `nV` for every `n >= 2`, the
same holds for every `nV` with `n >= 2`.

More precisely, for every infinite-order `g` in Thompson's group `V`, the
element `g × id` of `2V` (acting as `g` on the first coordinate of the Cantor
square and trivially on the second) has roots of every order inside `2V`, and
these roots can be chosen to generate a copy of `Q` containing `g × id`.

**Credit.** The result is due to S. Kojima and X. Sheng, *On subgroups of
Brin-Thompson groups nV*, arXiv:2603.18410 (v1 March 19, 2026; v3 May 23,
2026; unrefereed). Their Theorem 1.2 reads, verbatim from the v3 HTML: "For
n≥2, the Brin-Thompson group nV contains continuum many copies of the
additive group of the rationals ℚ sharing the subgroup isomorphic to ℤ". Their
construction uses horizontal slides with vertical shifting of dyadic blocks.
The proof route here is a self-contained explicit version: a mixed-radix
odometer in the second coordinate whose overflow applies an infinite-order
element of `V` in the first coordinate. It does not reprove the continuum
count.

**Contrast with V.** Kojima–Sheng record that G. Higman (*Finitely presented
infinite simple groups*, Notes on Pure Mathematics 8, ANU, 1974) showed that
`V` has no element of infinite order with roots of arbitrarily large order, so
`Q` does not embed in `V`. That statement is quoted from Kojima–Sheng and was
not checked against Higman's notes. The construction below needs the second
coordinate: it stores the fractional counter at bounded depth there, while in
`V` the counter would have to sit at unbounded depth.

**Consequences recorded elsewhere.**
- It answers Zaremsky Problem 2.19(e) yes, through `zaremsky-2-19e-by-yes`.
- It removes the "no infinitely divisible elements" obstruction, which holds
  for `V`, as a way to exclude subgroups of `nV` for `n >= 2`.
- Kojima–Sheng state, as their Corollary 4.3 (quoted, not re-derived here),
  that `nV` for `n >= 2` has no proper isometric action on a CAT(0) cube
  complex; their argument is a translation-length bound on roots. Callard–Salo
  state the same conclusion (arXiv:2208.00685v2, Corollary 1.2, imported in
  `brin-thompson-mv-contains-a-distortion-element`). Farley's cube-complex proof
  of the Haagerup property for `V` therefore does not extend verbatim (Problem
  2.7).
- Review: z-verify-groups PASS, 2026-09-13
  (`research/artifacts/zp-review-groups-2026-09-13-part1.md` §7, c0ff0a5f90).
