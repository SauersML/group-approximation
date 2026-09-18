---
rg: 2
id: relative-eg-pair-base-meets-its-conjugates-in-free-groups
kind: claim
title: If pd of the relative augmentation ideal I_{G/H} is at most 1, then H meets every conjugate gHg^{-1} with g outside H in a free group, and H_2(H) injects into H_2(G); so normal, commensurated, finite-index and HNN-vertex bases are excluded from the relative Eilenberg--Ganea problem
distinct_from:
  relative-countable-eg-gives-eg-for-aleph-one-groups: that shows pd I_{G/H} <= 1 is necessary for relative realization (Klein-bottle example); this derives structural consequences of that pd hypothesis for the pair itself, with no geometry.
  aleph-one-eg-is-equivalent-to-relative-countable-eg: that states the minimal-counterexample profile; this adds two algebraic items to it and eliminates candidate families wholesale.
  relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two: that is the geometric per-pair engine; this is a purely cohomological necessary condition on admissible pairs.
artifacts: []
---

**ESTABLISHED** through `relative-eg-pair-base-meets-its-conjugates-in-free-groups-proof`. Unreviewed. No novelty is claimed with confidence: the argument is a Mackey computation and may be folklore in Bieri--Eckmann relative cohomology.

## Statement

Let `H ≤ G` be groups (any cardinality) with `pd_{ZG} I_{G/H} ≤ 1`, where `I_{G/H} = ker(Z[G/H] → Z)`. No hypothesis on `cd G` is needed.

- **(A) Free conjugate intersections.** For every `g ∈ G ∖ H`, `cd(H ∩ gHg^{-1}) ≤ 1`, so `H ∩ gHg^{-1}` is free (Stallings–Swan).
- **(B) Homology injectivity.** `H_2(H;Z) → H_2(G;Z)` is injective.

## Corollaries (the refuter's reading)

Assume in addition `H` is not free (the only case that matters for the relative Eilenberg--Ganea problem, by the free-base lemma).

1. **Self-commensurating.** `Comm_G(H) = H` when `H` is torsion-free of finite cd (e.g. `cd G ≤ 2`). More strongly, if `U ≤ H` is not free and `gUg^{-1} ≤ H`, then `g ∈ H`. In particular `N_G(U) ≤ H` and `C_G(U) ≤ H` for every non-free `U ≤ H`.
2. **No normal bases.** If `H ⊴ G` and `H ≠ G`, the pd condition fails. This kills every fibre-type candidate: Bestvina–Brady kernels `ker(A_L → Z)` inside a 2-dimensional right-angled Artin group (connected triangle-free `L` with a cycle), fibres of mapping tori, and the Klein-bottle calibration `Z^2 ⊴ K`.
3. **No proper finite-index bases.** If `[G:H] < ∞` and `H ≠ G`, the pd condition fails.
4. **Baumslag–Solitar `BS(1,n)` (including `Z^2` and the Klein bottle group).** Every non-free subgroup has finite index, so the only admissible pairs with non-free base are `H = G`. No candidate lives here.
5. **HNN vertex groups.** If `G = ⟨B, t | t α(c) t^{-1} = β(c), c ∈ C⟩` with `C` not free, then `B ∩ tBt^{-1} ⊇ β(C)`, so `(B,G)` is not admissible. For an amalgam `A *_C B`, admissibility of `(A, A *_C B)` forces `C ∩ bCb^{-1}` free for all `b ∈ B ∖ C`.
6. **Free intersections are not sufficient.** `G = F(b,c) × Z` with `H = ⟨[b,c]⟩ × Z ≅ Z^2`: all `H ∩ gHg^{-1}` (`g ∉ H`) are `≅ Z`, but `H_2(H) → H_2(G)` is zero, so (B) shows the pd condition fails.

## Consequence for the minimal counterexample

The profile of `aleph-one-eg-is-equivalent-to-relative-countable-eg` gains two items: a countable pair `(H,G)` whose `ℵ_1`-fold amalgam is an Eilenberg--Ganea counterexample must have `H ∩ gHg^{-1}` free for all `g ∉ H` (so `H` is "malnormal modulo free" and self-commensurating) and `H_2(H) ↪ H_2(G)`. The candidate families of normal subgroups (Bestvina–Brady kernels, fibres) and of solvable cd-2 groups are dead as sources of relative counterexamples; a would-be counterexample base must look like a peripheral (boundary-type) subgroup.
