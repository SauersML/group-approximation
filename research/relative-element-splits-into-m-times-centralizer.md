---
rg: 2
id: relative-element-splits-into-m-times-centralizer
kind: claim
title: A relatively centralizing element splits as a Kazhdan-kernel element times an exact centralizer
distinct_from:
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that is the group-level relative criterion, a statement about commutators in H; this is the permutation-model splitting of the single element sigma(z) in the universal sofic group, which together with the Kun--Thom normalization theorem yields that criterion.
  sofic-groups-kill-rigid-compression-defects: that is the established absolute criterion, the case M = 1 where the splitting is just sigma(z) in C(sigma(Gamma)); this allows a normal Kazhdan subgroup M and asks the mod-M ambiguity to be absorbable into sigma(M).
  kun-thom-sofic-centralizer-normalization: that is the imported theorem that sigma(G) normalizes C(sigma(Gamma)); this is the extra input, an M-valued cocycle triviality, that the relative criterion needs beyond it.
---

**OPEN.** Let `H` be a countable sofic group, let `M` be a normal subgroup of
`H` with property (T), and let `M <= Gamma <= G <= H` be a rigid pair (`Gamma`
and `G` Kazhdan, `Gamma` infranormal in `G`). Fix a nonprincipal ultrafilter
`U`, a sequence of finite sets `(Y_n)`, and an injective sofic representation

```text
sigma : H -> S_U = prod_{n->U} Sym(Y_n),   tr(sigma(h)) = 0 for h != 1.
```

Then for every `z in H` with `[z, Gamma] <= M`,

```text
sigma(z)  in  sigma(M) . C_{S_U}(sigma(Gamma)),
```

that is, `sigma(z) = sigma(m_0) c` with `m_0` in the image of `M` and `c`
centralizing `sigma(Gamma)`.

## Why this is the hinge

`sigma(z)` normalizes `sigma(Gamma)`: from `[z, Gamma] <= M` we get
`z gamma z^-1 = gamma . m_gamma` with `m_gamma in M`, so
`sigma(z) sigma(gamma) sigma(z)^-1 = sigma(gamma m_gamma)` and `gamma m_gamma in Gamma`.
The map `gamma -> m_gamma` is a 1-cocycle for the `Gamma`-conjugation action,
valued in `M`. This claim asks exactly that the cocycle be a coboundary
realizable inside `sigma(M)`, up to an element that centralizes `sigma(Gamma)`
on the nose. It is the exact-algebra form of the "blockwise cocycle-conjugacy"
hinge recorded in `research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md`.

With `kun-thom-sofic-centralizer-normalization` (`sigma(G)` normalizes
`C(sigma(Gamma))`) this yields the relative criterion
`sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels` through the route
`relative-defect-via-normalizer-split`, hence a nonsofic hyperbolic group
(`nonsofic-hyperbolic-via-relative-rigid-defect`). Unlike the route
`relative-rigid-defect-from-kazhdan-quotient-permanence`, it never assumes
`H/M` is sofic: it works with one sofic representation of `H`.

The case `M = 1` is true and is the absolute criterion: the cocycle is
trivial, so `sigma(z) in C(sigma(Gamma))`.

## Attempts

- **Reduction to cocycle vanishing (this is what the claim is).** `sigma(M)`
  is a permutation action of a Kazhdan group with vanishing trace off the
  identity. After the `o(|Y_n|)` edge edit of Kun--Thom Lemma 2.3 the
  `M`-orbits ("blocks") carry expander Schreier actions. `sigma(z)` permutes
  the blocks and, within blocks, differs from an exact centralizer by the
  cocycle `gamma -> m_gamma`. The claim is that this cocycle is a coboundary
  into `sigma(M)`.
- **Property (T) cocycle rigidity, and where it fails.** If `gamma -> m_gamma`
  took values in a fixed unitary or amenable `Gamma`-module, the finitary
  `H^1`-vanishing of property (T) (Shalom; Delorme--Guichardet) would force
  the cocycle asymptotically to a coboundary, giving the correction. Here the
  coefficients are not a fixed module: they form the bundle over the block
  structure of `S_U`, a family of finite `M`-set actions with unbounded fibres
  and no linear structure. No `H^1`-vanishing theorem applies to that target.
  **This is where it stops.**
- **Trace-blindness (constraint, not progress).** In any trace-preserving
  model of `H`, `tr(sigma(w)) = 0` for `w in M \ {1}`, so the spectral measure
  of `M`'s Laplacian is that of the regular representation: a gap at `0` with
  no atom. The Kazhdan projection of `M` has trace `0`, so `H/M` acts on no
  nonzero corner of the tracial ultraproduct. Any proof must run on the
  diagonal (Koopman) side, on the block set, not on `l^2(Y_n)`.
- **Bounded-orbit sub-case (most promising).** If `M` acts in `sigma` with
  orbits of uniformly bounded size, the cocycle takes values in a bounded
  family of finite groups, and a Kun--Thom-style median/averaging argument over
  each block should produce the coboundary. Not completed here; it is the
  natural next target and would settle the sub-case where `M`'s isotropy is
  bounded.
