---
rg: 2
id: fp-kernel-crosses-alekseev-thom-open-problem
kind: claim
title: A finitely presented kernel in the split-cyclic target solves Alekseev--Thom Open Problem 6.1
distinct_from:
  torsion-free-sofic-exact-mf-radical-over-z: the base target requires finite presentation only of the total group; its Kazhdan kernel is automatically finitely generated but may be infinitely presented.
  torsion-free-lef-kazhdan-non-rf-seed: that established seed is torsion-free, LEF and Kazhdan but is necessarily not finitely presented because it is LEF and non-residually-finite.
artifacts:
  - research/artifacts/alekseev-thom-fp-kernel-boundary-2026-08-26.md
---

**ESTABLISHED REDUCTION.**  Suppose the target
`torsion-free-sofic-exact-mf-radical-over-z` is proved with the preferred
extra hypothesis that its normal Kazhdan kernel `K` is finitely presented.
Then

```text
K is finitely presented, sofic, property (T), and not residually finite.
                                                               (ATK1)
```

Thus this strengthening answers Open Problem 6.1 of Alekseev--Thom,
*Centralizers of sofic approximations of Kazhdan groups* (arXiv:2608.05362),
which asks whether a finitely presented sofic Kazhdan group can fail residual
finiteness.

Soficity passes from the target group `G` to its subgroup `K`.  Every extension
of `K` by `Z` splits after choosing a lift of `1`, so `G` is a mapping torus of
an automorphism of `K`.  If `K` were residually finite, property `(T)` would
make it finitely generated and
`finitely-generated-rf-automorphism-mapping-torus-is-rf` would make `G`
residually finite.  Then `G` would be operator-MF, contradicting
`Rad_MF(G)=K!=1`.  Hence `K` is not residually finite, proving `(ATK1)`.

This does not obstruct the base target.  It says that the efficient first goal
is a finitely presented total mapping torus with an infinitely presented
finitely generated kernel, exactly as allowed by the split-cyclic schema.

DERIVATION
fp-kernel-crosses-alekseev-thom-open-problem-proof
