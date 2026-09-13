---
rg: 2
id: zaremsky-4-06-f-infinity-finite-cd-contractible-rips
kind: claim
title: "Zaremsky Problem 4.6 resolved: does every group of type F_infinity with finite cohomological dimension have a contractible Rips complex?"
root: true
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is Zaremsky's question for the one group Z^n with its standard word metric, answered by Virk; this is the question for every group of type F_infinity with finite cohomological dimension, which contains the fp case of Bass's FP versus FF question
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for Z^n in the l^1 metric; this is Zaremsky's question over a whole finiteness class
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick theorem for hyperbolic groups; this is Zaremsky's question for all groups of type F_infinity with finite cohomological dimension
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4, Problem 6,
verbatim: "(Added 10/2/24): If a group is of type `F_∞` and has finite
cohomological dimension, then does it have a contractible Rips complex? (This
would imply it's of type F, so this would solve Problem 21 in Section 1
above.)"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-06-by-yes` requires
  `f-infinity-finite-cd-groups-have-contractible-rips`.
- **No**: `zaremsky-4-06-by-no` requires
  `some-f-infinity-finite-cd-group-has-no-contractible-rips`.

Never write a `requires: []` route into this claim.

**Reading.** `G` is a group of type `F_∞` (so finitely generated) with
`cd G < ∞`, hence torsion-free. "Has a contractible Rips complex" is read in the
weakest form: for SOME finite symmetric generating set `S` and SOME scale
`r ≥ 1`, the closed Rips complex `R_r(G,S)` (vertex set `G`, simplices the
finite subsets of `d_S`-diameter `≤ r`) is contractible. The stronger reading
"type `ℝ`" of Li–Sánchez Saldaña (arXiv:2608.24279): some `S` with `R_r(G,S)`
contractible for all sufficiently large `r`. A yes under the strong reading
gives a yes under the weak one; a no under the weak reading gives a no under the
strong one. The node `contractible-rips-complex-gives-finite-classifying-space`
proves the parenthetical remark: a contractible Rips complex of a torsion-free
group is the universal cover of a finite `K(G,1)`.

**Structure.** Write (1.21) for "every group of type `F_∞` with finite
cohomological dimension is of type F" (the list's second form of Problem 1.21)
and (4.7) for "every group of type F has a contractible Rips complex"
(Problem 4.7). Since type F implies `F_∞` and finite cd, and a contractible Rips
complex gives type F, a yes to 4.6 is exactly a yes to both (1.21) and (4.7).
A no comes either from a counterexample to (1.21) or from a type F group with no
contractible Rips complex.

**Status (bounded check, 2026-09-13).** Open. z-status-b's table
(`research/artifacts/zp-open-status-sections-2-4-2026-09-13-part*.md`)
records Li–Sánchez Saldaña arXiv:2608.24279 (type `ℝ` is closed under graphs
of groups with finite edge groups; two-dimensional RAAGs are of type `ℝ`) and
Hulbert–Zaremsky arXiv:2608.25614 (`VR_2(A_Γ)` contractible for triangle-free
`Γ`). Neither treats groups known only to be `F_∞` with finite cd.

## Attempts

- 2026-09-13 (z4-06-rips-finf-fcd): root decomposition above; see the two
  answer claims for the approaches and where they stop.
