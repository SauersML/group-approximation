---
rg: 2
id: km-hexagon-level-cokernel-is-nonzero
kind: claim
title: The product-cycle map has nonzero cokernel at hexagon twisted levels with parameter at most three
artifacts:
  - research/artifacts/km-opposition-connectivity-computations-2026-08-23.md
distinct_from:
  km-twisted-level-product-cycles-surject: that asserts surjectivity at every twisted level; this establishes its negation at the `G_2` levels by an explicit integral annihilator, refuting it as stated while leaving the grid and `B_2` levels' surjectivity standing.
  km-codistance-filtration-twisted-levels-are-rank-two-pairs: that computes the relative homology of the filtration levels in terms of this cokernel; this decides the cokernel's nonvanishing on the hexagon levels.
---

**THEOREM (established; proof in
`km-hexagon-level-cokernel-proof`).**  Let a twisted level of the
`(2,4,6)` codistance filtration have a `G_2` residue on at least one
side, with `A` the panel-opposition geometry of the split Cayley
hexagon residue (points at maximal distance from the panel line,
classed by their feet; lines the opposite lines).  Whenever the
one-class-deleted incidence graph of `A` is disconnected while the full
graph is connected -- verified by the axiom-checked computations for
`q = 2` (components `[24,24]` already for the full graph) and `q = 3`
(full graph connected, any deletion gives components `[81,81,81]`) --
the map

```text
H_1(A) (x) H_1(B) --> (+)_(matched-class pairs) Z_1(K_(q,q))
```

of `km-codistance-filtration-twisted-levels-are-rank-two-pairs` (d) has
NONZERO cokernel, integrally and rationally.

**Scope (corrected same day by the `H(4)` computation).**  The
hypothesis -- one-class-deleted disconnection -- holds EXACTLY for
`q <= 3`: the class-stabilizer subgroups map to the points of a
rational normal cubic in the Frattini quotient `F_q^4` of the
line-parabolic radical (a Vandermonde argument valid in every
characteristic), so the walk graph on `k` classes has
`q^(max(0, 4-k))` components; the full graph is connected iff
`q >= 3` and the one-deleted graphs iff `q >= 4`.  This law reproduces
every computed component pattern at `q = 2, 3, 4` (including
`[1024]`, four times `192`, sixteen times `32` at `q = 4`).  An
earlier note predicting a characteristic-two collapse for all even `q`
rested on using adjoint structure constants for the seven-dimensional
module (whose relevant matrix element is `±1` on a two-string) and is
RETRACTED; `H(4)` is connected at every deletion depth predicted.

**Consequences.**  For the actual Kac--Moody lattices (`q > 1764^3`)
these annihilators are vacuous; the small-`q` refutations instead
calibrate the thresholds of the disjoint-class surjectivity
construction: `B_2` levels need `q >= 6`, hexagon levels need four
intermediate classes on each side, so `q + 1 >= 9`.  For `q >= 8`, in
any characteristic, the construction applies at every twisted level,
and the conditional chain (type `F_3`,
`H^2(Lambda;Z Lambda) = 0`, death of Ioana--Spaas--Wiersma Corollary D)
is restored, pending only the single-slot bookkeeping recorded in
`km-twisted-level-product-cycles-surject`.
