---
rg: 2
id: long-root-central-product-has-exact-maslov-models
kind: claim
title: The two long-root central product has exact finite-dimensional models in both nontrivial Maslov sectors
artifacts:
  - research/artifacts/long-root-central-product-maslov-model-2026-08-21.md
distinct_from:
  c2-root-commuting-cycle-is-maslov-trivial: that splits the Deligne multiplier on the abelian root graph product; this allows the full rank-one central extensions and proves that their common-center product still has exact nontrivial-sector matrix representations.
  maslov-finite-subgroup-atlas-no-go: that balances projective regular multiplicities on arbitrary finite subgroup atlases; this constructs genuine representations of one infinite central-product subgroup with the global central mark acting by a prescribed nontrivial scalar.
  mihailova-free-rounding-projective-cross-fence: that isolates ordinary and projective cross-stability for two free actors; this no-go remains valid even if cross synchronization is granted perfectly.
---

Let `E_beta,E_delta < E_3` be the inverse images of the two commuting
long-root copies of `SL2(Z)` in the Deligne three-cover, where
`delta=2alpha+beta`.  Then

```text
P=<E_beta,E_delta>
  =(E_beta x E_delta)/<(z,z^(-1))>,
```

and for each `j=1,2` there is an exact finite-dimensional representation

```text
rho_j:P -> U(d_j),       rho_j(z)=omega^j I.
```

Consequently exactifying the two rank-one factors, matching their cyclic
overlap, and making their images commute cannot force the Maslov scalar to
collapse.  Any gap proof must use mixed noncommuting `C2` Chevalley relations
outside `P`.

The proof is `long-root-central-product-maslov-model-proof`.

