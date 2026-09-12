---
rg: 2
id: non-enlarging-sofic-window-cascades-cannot-compress
kind: claim
title: A cascade of routing, measure-preserving and sofic-window stages that never enlarges the alphabet preserves the uniform measure and never compresses
distinct_from:
  single-maximal-stage-routed-codes-cannot-compress: that allows one combining stage between routings; this allows any number of combining stages along different sofic windows, which may together generate a nonsofic group such as the Leavitt units, provided no stage enlarges the alphabet.
  injective-same-alphabet-sofic-codes-preserve-uniform-measure: that is the rigidity of one equal-alphabet code over a sofic group; this composes it along a cascade over an arbitrary group and locates where a compressing cascade must enlarge and shrink the alphabet.
artifacts:
  - research/artifacts/non-expanding-sofic-cascades-2026-09-12.md
---

Let `G` be countable and `tau = S_k o ... o S_1` a composite of Borel equivariant codes
`S_i: E_(i-1)^G -> E_i^G`, with `E_0 = A` and `E_k = B`. Each stage is one of:
- (R) a routing code;
- (P) an equal-alphabet code carrying the uniform measure to the uniform measure, such as a bijective automaton;
- (W) a code with window in a sofic subgroup `K_i`.

The windows may together generate any subgroup, for instance all of `U = L_(F_2)(1,2)^x`. Suppose `tau` is
injective on a conull set, and put `nu_i = (S_i o ... o S_1)_* mu_A`.

1. The first alphabet change is an enlargement at a (W)-stage, and every earlier `nu_i` is uniform.
2. If no stage enlarges the alphabet, every `nu_i` is uniform and `|B| = |A|`, so there is no compression.
3. A (W)-stage that shrinks the alphabet reads a non-uniform measure.
4. The output of the first enlarging stage is not uniform on any coset of its window.
5. A last stage with window in a Rokhlin-maximal subgroup is allowed. After alphabet-keeping stages it gives
   `|B| >= |A|`.

**Reading for `measurable-alphabet-compression-over-leavitt-units`.** A compression built from such stages must
enlarge before it shrinks, like an error-correcting code: redundancy along one sofic window, spent along another
through relations of `U` between the windows.

**Sharpness.** Enlarging stages along the cyclic subgroups `<w_i>` realize every continuous code with window
`{w_1, ..., w_m}` (Proposition H), so no stage-counting theorem covers enlarging cascades without deciding
continuous compressions.

**Remark.** A compression with continuous encoder and continuous decoder is a strict automaton (artifact,
Section 4).

Proof: Sections 3–4 of the artifact, route `non-enlarging-sofic-cascades-proof`.

**ESTABLISHED 2026-09-12** by [[non-enlarging-sofic-cascades-proof]]. Verification requested from
w3-vf-nonlinear.
