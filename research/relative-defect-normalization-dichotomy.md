---
rg: 2
id: relative-defect-normalization-dichotomy
kind: claim
title: Killing rigid defects modulo Kazhdan kernels is equivalent to normalizing relative centralizers in the universal sofic group
distinct_from:
  rigid-compression-defect-normalization-dichotomy: that is the absolute equivalence DD <=> NORM, the case M = 1 where the relative centralizer is the exact centralizer; this is the relative equivalence, with the group of permutations normalizing sigma(M) whose commutators with sigma(Gamma) land in sigma(M).
  relative-element-splits-into-m-times-centralizer: that proposed the splitting sigma(z) in sigma(M).C(sigma(Gamma)), which fails for outer automorphisms of Gamma trivial modulo M; this is an exact equivalence that assumes no splitting.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma <= G` be a rigid pair (`Gamma`, `G` Kazhdan,
`Gamma` infranormal in `G`) and `M` a Kazhdan subgroup of `Gamma` normal in
`G`. For a homomorphism `sigma : G -> S_U` into the universal sofic group put

```text
N_rel(sigma) = { x in S_U : x sigma(M) x^-1 = sigma(M),
                            [x, sigma(gamma)] in sigma(M) for all gamma in Gamma } .
```

This is a subgroup of `S_U`. Put

```text
RDD:   for every countable sofic H, every Kazhdan M normal in H, and every rigid
       pair M <= Gamma <= G <= H:
       [z, Gamma] <= M  ==>  [g z g^-1, gamma] in M   (z in H, g in G, gamma in Gamma).
RNORM: for every such pair and M, and every homomorphism sigma : G -> S_U,
       sigma(G) normalizes N_rel(sigma).
```

Then `RDD <=> RNORM`. Derivation: `relative-defect-normalization-dichotomy-proof`.

- A failure of `RNORM` at `(sigma, x)` yields the countable sofic group
  `<sigma(G), x> <= S_U`, which contains the relative configuration
  `sigma(M) <= sigma(Gamma) <= sigma(G)` and has a nontrivial defect modulo
  `sigma(M)`.
- `M = 1`: `N_rel(sigma) = C_{S_U}(sigma(Gamma))`, so `RNORM` is `NORM(sofic)`.
  Kun--Thom Theorem 4.1 (`kun-thom-sofic-centralizer-normalization`) gives it
  only for trace-zero sofic representations. `rigid-compression-defect-normalization-dichotomy`
  extends it to every homomorphism. `RDD` is then the established
  `sofic-groups-kill-rigid-compression-defects`.
- Conjugation by `sigma(Gamma)` always preserves `N_rel(sigma)`, because
  `Gamma` normalizes `M`. Only the strict compressors carry content.
- `RDD` is `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`, and
  `RNORM` is `relative-normalization-modulo-kazhdan-kernel`. With
  `nonsofic-hyperbolic-via-relative-rigid-defect`, `RNORM` would give a
  nonsofic hyperbolic group.
