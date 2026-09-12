---
rg: 2
id: relative-defect-iff-surjective-compressor-endomorphisms
kind: claim
title: In a sofic host the relative defect vanishes iff compressors induce surjective endomorphisms of the relative centralizer quotient
distinct_from:
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that is the open relative criterion for every sofic host; this reduces one configuration to surjectivity of explicit injective endomorphisms of a single quotient group, with no ultraproduct, and proves the criterion whenever that quotient is co-Hopfian.
  relative-defect-normalization-dichotomy: that is the ultraproduct equivalence RDD <=> RNORM over all configurations; this is an algebraic equivalence inside one fixed sofic host.
  relative-defect-criterion-holds-for-finite-compression-cores: that proves the criterion when some compression core is finite, which forces the kernel to be finite; this allows an infinite kernel and asks only that the relative quotient be co-Hopfian, for instance finite.
  defect-forces-proper-self-embedding: that forces a proper self-embedding of the compressed core in the absolute setting; this forces a proper self-embedding of the relative centralizer quotient, a different group, and uses the absolute sofic criterion as its input.
  relative-element-splits-into-m-times-centralizer: that is the refuted splitting, which asks the quotient to be trivial; this tolerates every quotient on which the compressors act surjectively, including the finite quotient of the transpose-inverse example.
---

**ESTABLISHED.** Let `H` be a countable sofic group, `M` a normal subgroup of
`H`, and `Gamma <= G <= H` a rigid pair (`Gamma` and `G` Kazhdan, `Gamma`
infranormal in `G`) with `M <= Gamma`. Put

```text
Z = { z in H : [z, gamma] in M for all gamma in Gamma },   K = M . C_H(Gamma),   Q = Z / K.
```

1. `Z` is a subgroup of `H` normalizing `Gamma`, and `K` is normal in `Z`.
2. For every compressor `t in P_Gamma` one has `t^-1 Z t <= Z` and
   `t^-1 K t = K`. So `z K -> t^-1 z t K` is a well-defined **injective**
   endomorphism `eps_t` of `Q`.
3. The following are equivalent:
   - `[g z g^-1, gamma] in M` for all `g in G`, `gamma in Gamma`, `z in Z`,
     i.e. the relative criterion holds for this configuration;
   - `G` normalizes `Z`;
   - `eps_t` is surjective for every `t in P_Gamma`.
4. **Co-Hopfian quotients.** If `Q` is co-Hopfian, in particular if
   `[Z : M . C_H(Gamma)]` is finite, the relative criterion holds for the
   configuration.

Property (T) of `M` is not used; only the absolute criterion for the pair
`Gamma <= G` enters. Derivation: `relative-defect-compressor-endomorphism-proof`.

## Consequences

- **What a counterexample needs.** A sofic host refuting
  `sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`, in addition to the
  profile in `relative-defect-criterion-holds-for-finite-compression-cores`,
  needs an infinite relative quotient `Q` and a compressor `t` for which
  `eps_t` is a proper self-embedding. So `Q` is not co-Hopfian.
- **The transpose-inverse example.** For `H = SL_3(Z) semidirect <alpha>` with
  `alpha` the transpose-inverse and `M = Gamma = G = SL_3(Z)`, one gets
  `Q = H/SL_3(Z) = Z/2`. It is finite, so the criterion holds. The refuted
  splitting failed only because `Q != 1`; this theorem is its repair in
  finite-index form, and tolerates finitely many outer classes trivial
  modulo `M`.
- **The Leavitt cover is not excluded.** For
  `hyperbolic-kazhdan-cover-of-leavitt-unit-group`, with `M = N`,
  `Gamma_hat = pi^-1(EL_alpha(R))` and `G_hat = pi^-1(EL_D(R))`:
  - `Z = pi^-1(C_(R^x)(EL_alpha(R)))`;
  - `C_G(Gamma_hat)` is finite, since `Gamma_hat` is non-elementary
    (`hyperbolic-compression-centralizer-rigidity`), and the cover is
    torsion-free, so `K = N`;
  - hence `Q = C_(R^x)(EL_alpha(R))`, which contains `V_(1000)`, a copy of
    Thompson's `V`;
  - by `leavitt-unit-group-carries-nontrivial-rigid-defect`, `eps_u_hat` is not
    surjective.

  So `Q` is not co-Hopfian and this theorem certifies nothing about the cover,
  as it must while the cover's soficity is open. The cover's relative defect
  is exactly the proper self-embedding `z -> u^-1 z u` of
  `C_(R^x)(EL_alpha(R))`. A proof that the cover is nonsofic has to show that
  no sofic host realizes such a strict compressor self-embedding over a
  Kazhdan kernel.
