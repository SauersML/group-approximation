---
rg: 2
id: amplification-natural-block-size-selectors-cannot-be-tight
kind: claim
title: Amplification-natural block-size selectors cannot form a tight multiplicity checksum
distinct_from:
  amplification-natural-words-cannot-read-packet-multiplicity: that proves normalized words and PI degree cannot read raw multiplicity; this derives the direct contradiction with pairwise orthogonal exhaustive size selectors.
  canonical-tight-multiplicity-block-checksum: that is the remaining positive compiler target; this proves its selectors must be genuinely matrix-coordinate or otherwise amplification-nonnatural.
  orthogonal-checksum-controls-only-mass-weighted-syndromes: that permits valid authenticated blocks with escaping mass; this shows ordinary word-defined raw-size blocks cannot even have the intended authentication semantics.
---

ESTABLISHED NO-GO.  Let a fixed finite packet have a nonzero `pi`-carrier
`P(U)` in an exact representation `U`, with multiplicity `k`.  Suppose
`P_n(U)` are pairwise orthogonal projections, natural under spectator
amplification,

```text
 P_n(U tensor I_l)=P_n(U) tensor I_l,                    (ANS1)
```

and are claimed to authenticate raw multiplicity:

```text
 P_k(U)=P(U),       P_n(U)=0 for n!=k.                  (ANS2)
```

No such family exists for all finite multiplicities.  Indeed `U tensor
I_l` has multiplicity `kl`, but `(ANS1)--(ANS2)` simultaneously give

```text
 P_k(U tensor I_l)=P(U) tensor I_l !=0
```

and require it to be zero because `k!=kl`.  Equivalently the `k` and `kl`
selectors would both equal the amplified carrier, contradicting their
orthogonality.

Every projection obtained from a fixed group word, group-algebra matrix,
finite functional-calculus packet, or fixed finite normalized word-statistic
decision rule satisfies `(ANS1)`.  Consequently the canonically tight
checksum cannot be implemented by a static library of such selectors.  It
must use an amplification-nonnatural matrix coordinate, an irreducibility
test not expressible by normalized group-word semantics, or abandon raw
multiplicity in favor of a canonically prescribed type variable.

