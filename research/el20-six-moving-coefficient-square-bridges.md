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
- The sharper factorization is now explicit in
  `literal-whiteheads-give-gauged-moving-bridge-table`: each `v_i` normalizes
  the signed Hecke source, so `J_i` alone and its six Singer conjugates have
  exact full Grams and exact mixed squares.  But `J_i` is the literal native
  Whitehead occurrence defining the stage discrepancy, so those bridges
  type as `N_(i,k) tensor D_(i,k)`, not as ungauged coefficient bridges.
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
- Refining each moving cut by a Singer-normalized incoming-root Lagrangian
  does not turn that subgroup mismatch into a character mismatch.  By
  `incoming-lagrangian-refinement-preserves-hecke-actor-support`, an affine
  stabilizer refinement still has actor support `t_i^kL_0t_i^(-k)`.  A
  dual Pauli translation preserves this subgroup support and changes at
  most its character/cocycle, whereas the next stage has the genuinely
  different subgroup `t_i^(k+1)L_0t_i^(-(k+1))`.
- The canonical full-Leavitt escape also has the wrong support, for a
  different exact reason.  By
  `leavitt-compression-preserves-root-position-support`, the compression
  endomorphism `x_ab(r) |-> x_ab(s_0rt_0)` and its explicit 20-by-20
  Whitehead implementation preserve every ordered root position.  The
  Singer step sends the actual `(2,8)` root of `L_0` to `(2,7)`, so the
  compression cell sends `Q` to the Reynolds cut over `alpha(L_0)` rather
  than to `t_iQt_i^(-1)`.  Its Singer conjugates therefore fail `(ESB1)`
  before the mixed-square estimate is reached.
- Dressing the literal Whitehead by any collection of already ungauged
  source/range normalizers cannot repair `(ESB2)`.  By
  `label-only-dressing-cannot-ungauge-a-whitehead-bridge`, a composite with
  exactly one gauged Whitehead occurrence is still typed `N tensor D`, and
  its distance from the required `N tensor 1` is exactly `||D-1||_2` up to
  the accumulated chart errors.  A successful composite therefore needs a
  second genuinely gauged mixed/opposite-root occurrence whose reservoir
  action cancels `D` while its total label action still moves the signed
  Hecke source exactly once; pure normalizer dressing is not enough.
- Adding that second gauge-bearing occurrence inside a larger **finite
  normal extraspecial packet** also fails.  By
  `finite-extraspecial-mixed-words-cannot-ungauge-singer-transport`, all
  outer reservoir factors multiply to the projective operator indexed by
  the total quotient element.  Moving `L_0` to `t_iL_0t_i^(-1)` forces that
  quotient element to be nontrivial, while universal cancellation of the
  reservoir factor forces it to be trivial.  This covers any finite number
  of mixed normalizer letters, not merely one Whitehead plus label-only
  dressing.
- The first genuinely nonnormal full-Leavitt candidate is also now exact
  and fenced.  Rootwise compression sends
  `W_87(s_0,t_0)` to `J_1` and the depth-one analogue to `J_2`, so the
  Hilbert-hotel conjugate has the correct full Gram.  By
  `compression-preimage-whitehead-preserves-gauge`, however, the two
  compression letters only change the source and range charts: the
  preimage gauge is conjugated to the literal Whitehead gauge.  Exact
  finite amplifications retain any nontrivial involution on both sides.
  Iterating the preimage only pushes that gauge to greater prefix depth.

The smallest remaining algebraic search is therefore explicit: find one
genuinely nonnormal coefficient/root-opposite word with the full-Gram property
`(ESB1)--(ESB2)` and verify its six Singer conjugate squares.  It must contain
an occurrence which exits the finite extraspecial atom algebra, not only
normalizer letters inside a larger finite packet.  No Property `(T)`, canonical
trace profile, or tracial-von-Neumann extension is allowed.
