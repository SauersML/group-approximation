---
rg: 2
id: compressed-doubles-raise-cohomological-dimension
kind: claim
title: A double over a subgroup with a compressor outside it has larger cohomological dimension, so no Kun--Thom double lives in a torsion-free group of dimension two
distinct_from:
  kazhdan-compression-instances-have-infinite-vcd: that excludes the commuting-factor criterion and lamp wreath products in every finite virtual dimension; this excludes Kun--Thom doubles in dimension two, which is the one recorded certificate that does occur in finite dimension.
  cd-two-group-with-infranormal-kazhdan-pair: that shows the pairs themselves exist in dimension two; this shows their doubles cannot, so pairs and doubles separate exactly there.
  fp-torsion-free-nonsofic-group-of-cd-at-most-three: that bounds the dimension of one nonsofic double above by three; this bounds every such double below by three, so that group has dimension exactly three.
---

**ESTABLISHED (unreviewed).**

**(DB1)** Let `Gamma <= G` with `n = cd Gamma < infinity`. Suppose some `u in G \ Gamma` satisfies
`u Gamma u^-1 <= Gamma`. This covers every strict compressor, and every element normalizing
`Gamma` from outside. Then

```text
cd(G *_Gamma G) >= n + 1.
```

**(DB2)** Let `K` be torsion-free with `cd K <= 2`, and let `Gamma <= G <= K` be Kazhdan, with
`Gamma` infranormal and not normal in `G`. Then `G *_Gamma G` does not embed in `K`.

*Why (DB2) follows.*
- `Gamma` is infinite by `infranormal-nonnormal-has-infinite-compression-orbit`, torsion-free, and
  not free, since it is Kazhdan. So `cd Gamma = 2`.
- A strict compressor lies outside `Gamma`: if it lay inside, conjugation would preserve `Gamma`.
- So (DB1) gives `cd(G *_Gamma G) >= 3 > cd K`.

## Consequences

- **Every recorded certificate is vacuous in dimension two.** In a torsion-free group of
  cohomological dimension two, such as a Titz Mite--Witzel kernel or `pi_1` of a finite
  non-positively curved square complex, no subgroup is:
  - an instance of the expander-matching criterion
    (`vcd-two-groups-contain-no-kazhdan-commuting-pairs`);
  - a generalized wreath product with an infinite lamp set (same node, (CD3));
  - a Kun--Thom double of an infranormal non-normal Kazhdan pair (DB2).
- **Pairs versus doubles.** The pairs do exist in dimension two
  (`cd-two-group-with-infranormal-kazhdan-pair`). Kun--Thom Theorem C and Corollary D act through
  actions, so they are unaffected: `groups-containing-kun-thom-pair-have-nonsofic-actions` gives
  such groups nonsofic actions, not nonsoficity.
- **Exact dimension of the recorded double.** The double of
  `fp-torsion-free-nonsofic-group-of-cd-at-most-three` has cohomological dimension exactly three.
- **Not covered.** Rigid compression defects (`sofic-groups-kill-rigid-compression-defects`)
  whose centralizing element has a power in the centre of `Gamma`. When `<z>` meets `Gamma`
  trivially, (CD2) already makes `z` trivial.

Proof: `compressed-doubles-raise-cohomological-dimension-proof`.
