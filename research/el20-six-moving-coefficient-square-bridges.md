---
rg: 2
id: el20-six-moving-coefficient-square-bridges
kind: claim
title: EL20 supplies six ungauged coefficient bridges between the order-seven moving cuts
distinct_from:
  six-ungauged-moving-squares-lock-seven-gauges: that proves the abstract quantitative gauge lock after bridges are authenticated; this asks for the actual EL20 words and full-Gram estimates.
  primitive-native-hecke-relators-have-no-odd-mixed-occurrence: that audits the primitive fixed relators between the original native and Hecke rows; this permits derived conjugate words acting between moving stages.
  middle-index-order-seven-orbit-cut-is-native-scale-neutral: that closes the fixed Fano actor packet; this requires bridges which retain the signed unequal-scale source rather than its scale-neutral constant atom.
---

**OPEN SIX-BRIDGE COEFFICIENT INTERFACE.**  In the setting of
`growing-multicut-el20-order-seven-inheritance`, construct for each row
`i=1,2` and `0<=k<=6` an ordinary EL20 coefficient word whose compression

```text
R_(i,k):E_(i,k)H -> E_(i,k+1)H                       (ESB1)
```

has source and range Gram equal to the corresponding moving cuts up to
`o_2(1)`, is typed in the adjacent packet charts as

```text
N_(i,k) tensor 1+o_2(1),                              (ESB2)
```

and participates in the mixed square

```text
C_(i,k+1)R_(i,k)=R_(i,k+1)C_(i,k)+o_2(1),            (ESB3)
```

with the exact label covariance `(SGL4)` for `0<=k<=5`.  All bridge and
square errors must be charged to one fixed finite ordinary-relator menu, with
dimension-independent constants.  A single base bridge is sufficient if
its six conjugates are authenticated with the same estimates.

The bridge must be coefficient-sensitive and ungauged on the multiplicity
factor.  Actor covariance alone only produces the order-seven holonomy of
`fano-moving-packet-retains-actor-holonomy`; independent stage typing leaves
the coboundary drift of
`moving-order-seven-stage-gauges-have-coboundary-drift`.

## Attempts

- The head `T_i` itself gives a full-Gram parallel transition, but carries
  the very reservoir gauge being measured, so its square is tautological.
- The seven-pair Fano packet gives ungauged root operators on its full label
  factor.  No established calculation shows that any such root has full
  source Gram from the signed Hecke character cut to its next Singer
  translate.  The only invariant Fano atom currently known is orthogonal to
  that signed source and collapses both native scales to `1/1`.
- A bridge built only from the finite actor group is insufficient: tensoring
  the actor table with its regular representation inserts a nontrivial
  order-seven reservoir holonomy while preserving every such covariance.
- Enlarging that search to the whole finite Fano semidirect packet still
  fails by `fano-semidir-bridges-are-wrong-subgroup-or-gauged`.  Pure
  coefficient words are ungauged but preserve the actor-subgroup Fourier
  support `L_0`, while the Singer stage uses `t_iL_0t_i^(-1)`.  Any word
  which moves this support has nontrivial actor quotient and reacquires the
  regular-amplification gauge.

The smallest remaining algebraic search is therefore explicit: find one
coefficient/root-opposite word with the full-Gram property `(ESB1)--(ESB2)`
and verify its six Singer conjugate squares.  No Property `(T)`, canonical
trace profile, or tracial-von-Neumann extension is allowed.
