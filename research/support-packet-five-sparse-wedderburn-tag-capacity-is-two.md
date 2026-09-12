---
rg: 2
id: support-packet-five-sparse-wedderburn-tag-capacity-is-two
kind: claim
title: The order-128 support packet has only two pointwise allowed-flat forbidden tags through five summands
artifacts:
  - experiments/support_packet_wedderburn_tag_capacity.py
  - experiments/support_packet_wedderburn_tag_capacity_4.json
  - experiments/support_packet_wedderburn_tag_capacity_5.json
  - experiments/run_support_packet_capacity.sbatch
distinct_from:
  support-packet-covariant-wedderburn-detector: that constructs two coefficients with equal allowed commutants and different forbidden commutants; this proves that capacity is sharp and remains exactly two throughout the complete sparse search.
  clifford-radical-antiphase-routing-has-character-capacity: that gives an all-coefficient character bound for Weyl/Clifford routing; this is a finite exhaustive bound for a non-character Wedderburn decoder and is deliberately limited to coefficients with at most five irreducible summands.
  support-packet-literal-tensor-covariance-is-blind: that rules out literal tensor covariance for arbitrary coefficients and automorphism twists; this permits commutant detection but shows its pointwise allowed-flat sparse tag class has size at most two.
---

Let `B_sub` be the order-128 support packet and let a coefficient `V` be a
direct sum of at most five packet irreducibles, counted with multiplicity.
Classify coefficients by

1. their Hilbert dimension; and
2. the complete unitary-conjugacy type of
   `End_B(S tensor V)` for each of the twelve irreducible sources `S` over
   the three allowed marked central characters `100,110,111`.

For every resulting pointwise allowed-equivalence class, count the distinct
unitary-conjugacy types of `End_B(T_101 tensor V)` on the unique forbidden
simple.  Exact exhaustive enumeration gives:

```text
summands   coefficients   allowed classes   capacity 1   capacity 2   maximum
   4          101270            905              697          208          2
   5          850668           3483             2578          905          2. (S5C1)
```

The seven-dimensional pair

```text
3*1+T_011,             3*1+T_101                         (S5C2)
```

already realizes the maximum.  Adding a fifth irreducible summand produces
more allowed profiles but no third forbidden Wedderburn type.

The computation constructs all 38 irreducible characters, uses the exact
fusion multiplicities, and encodes each embedded commutant by the multiset of
`(multiplicity,target-simple-dimension)` pairs.  Allowed keys are stored by
lossless compression, not probabilistic hashing.  The five-summand run used
one CPU on MSI node `acn112`, completed in 239 seconds, and used 12.9 MB RSS.

This closes the most direct sparse enrichment of the current detector: one
pointwise allowed-flat coefficient class cannot label the five V4 failure
occurrences by five different forbidden commutants in this range.  It does
**not** prove an all-coefficient fusion-ring theorem, and it does not quotient
allowed profiles by arbitrary source permutations induced by packet
automorphisms.  Those are strictly broader questions.  The immediate route
should therefore seek either a theoretical all-coefficient bound, an
automorphism-covariant classification, a different packet, or a contextual
cross-copy operation—not a blind six-summand brute-force extension.
