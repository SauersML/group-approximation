---
rg: 2
id: atlas-four-leg-frame-is-terminal-defect-gap
kind: claim
title: The Atlas four-leg frame target is quantitatively equivalent to a uniform packet-defect gap
distinct_from:
  atlas-four-leg-coordinate-frame-extraction: that asks for the four projections and comb unitary; this proves that their asserted inequalities contain no smaller coordinate-extraction content than the terminal defect gap.
  atlas-one-cut-finite-multiplicity-extraction: that asks for an asymmetric cut produced from every packet model; this identifies the scalar gap already forced by the more explicit four-leg formulation.
---

**ESTABLISHED.**  Consider any family of finite-multiplicity Atlas instances
with packet defect `delta`.  Assume, as in
`atlas-four-leg-coordinate-frame-extraction`, that a coefficient comb unitary
is available in a fixed matrix amplification.  The following are equivalent,
up to changing constants.

1. There are fixed `C,c>0` such that every instance admits equal-trace
   projections `E_1,...,E_4` and a coefficient comb unitary `W` satisfying
   `(FCF1)--(FCF2)`.
2. There is a fixed `epsilon>0` such that every instance has
   `delta>=epsilon`.

More precisely, (1) implies

```text
delta >= (1/(128 C))^(1/c).                           (FTE1)
```

Conversely, if (2) holds, then for any fixed `c>0`, the standard four
coordinate projections in a fourfold amplification and any available comb
unitary satisfy `(FCF1)--(FCF2)` with

```text
C = 1/(4 epsilon^c).                                  (FTE2)
```

Thus no noncanonical finite-multiplicity frame can make the four-leg claim a
strictly smaller intermediate theorem.  Proving that claim already proves
the terminal uniform defect gap; once that gap is known, the asserted frame
exists for the vacuous reason that its error allowance dominates every
possible forbidden-row mass.
