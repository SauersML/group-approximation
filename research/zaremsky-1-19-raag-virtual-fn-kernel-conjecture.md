---
rg: 2
id: zaremsky-1-19-raag-virtual-fn-kernel-conjecture
kind: claim
title: "Zaremsky Problem 1.19 resolved: if a finite-index subgroup of a right-angled Artin group maps onto Z with kernel of type F_n, does the group itself?"
root: true
distinct_from:
  zaremsky-1-05-artin-groups-are-type-f-infinity: that asks whether every Artin group has a classifying space with finite skeleta; this asks which normal subgroups with quotient Z of a right-angled Artin group, or of its finite-index subgroups, have type F_n.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 19, verbatim:
"Conjecture: If a right-angled Artin group has a finite index subgroup that maps
onto Z with kernel of type Fn, then so does the right-angled Artin group itself."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-19-by-yes` requires `raag-virtual-fn-kernel-implies-raag-fn-kernel`.
- **No**: `zaremsky-1-19-by-no` requires `some-raag-virtual-fn-kernel-without-raag-fn-kernel`.

Never write a `requires: []` route into this claim.

**Reading.** `L` is a finite flag complex with vertex set `V`, and `A_L` is the
right-angled Artin group with generators `V` and a commutation relation for each
edge of `L`. The conjecture is a statement for each `n ≥ 1`, and "type F_n" is the
homotopical property: a `K(G,1)` with finite `n`-skeleton. The hypothesis is: some
subgroup `H ≤ A_L` of finite index admits an epimorphism `ψ: H → Z` whose kernel is
of type `F_n`. The conclusion is: some epimorphism `χ: A_L → Z` has kernel of type
`F_n`.

**Background on the conclusion.** Let `BB_L` be the Bestvina--Brady kernel, the
kernel of the map `A_L → Z` sending every generator to `1`. M. Bestvina and
N. Brady (Invent. Math. 129 (1997)) proved that `BB_L` is of type `F_n` iff `L` is
`(n−1)`-connected, and of type `FP_n(R)` iff `L` is `(n−1)`-acyclic over `R`. For
`n = 2` the list itself notes, under Problem 1.23, that if some kernel of a map
`A_L → Z` is finitely presented then `BB_L` is; this comes from the Σ-invariant
computation of J. Meier, H. Meinert and L. VanWyk (Comment. Math. Helv. 73 (1998)).
Both statements are recorded here from memory of the sources and still have to be
checked against them before any citation route is written.

**Size of the question.** A finite-index subgroup `H` has more characters than
`A_L` (its first Betti number is usually larger), and the Morse functions on the
finite cover of the Salvetti complex that realize them need not come from
characters of `A_L`. The conjecture says none of these extra characters can have
better kernels than the best character of `A_L`.

**Status (2026-09-13, UNREVIEWED): answer yes, pending one citation import.**

- `raag-finite-index-sigma-m-forces-connected-flag-complex`: if a finite-index subgroup `H` has
  `Σ^m(H) ≠ ∅`, then `L` is `(m−1)`-connected (over a ring `R`: `(m−1)`-acyclic). A kernel of type
  `F_n` puts the character in `Σ^n(H)`, so `L` is `(n−1)`-connected, and Bestvina--Brady gives a kernel
  of type `F_n` for `A_L` (route `raag-virtual-fn-kernel-conjecture-via-sigma-invariants`).
- The route waits on `bestvina-brady-kernel-finiteness-theorem`, which is open until its
  statement is read from the source, so this root does not yet compile as established.
- Independent partial results: the homological form through division-ring Betti numbers
  (`raag-virtual-fp-n-kernel-forces-acyclic-flag-complex`) and the case `n = 1` with an elementary
  proof (`raag-virtual-fg-kernel-implies-fg-kernel`).

## Attempts

- 2026-09-13, lane z1-19-raag-kernel: Betti numbers over division rings do not see
  which character was chosen and scale with the index, so they transfer information
  from `H` back to `A_L`. Computed for every finite-index subgroup of `A_L` from the
  Salvetti complex (`raag-skew-field-betti-numbers-of-finite-index-subgroups`); a kernel of
  type `FP_n(F)` kills them in degrees `≤ n` for a Malcev--Neumann division ring
  (`bi-orderable-fp-n-fibre-kills-malcev-neumann-homology`). This settles everything except
  `π_1(L)`. Details: `research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md`.
