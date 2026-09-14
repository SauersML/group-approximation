---
rg: 2
id: kms-hbc2-genus-two-surface-subgroups-proof
kind: route
title: An integer-labelled girth surface verified in faithful integral models covers G_HBC2(2)(p) for p >= 7, and an F_5-labelled one verified in faithful mod-5 models covers p = 5
target: kms-hbc2-groups-contain-genus-two-surface-subgroups
requires: [kms-girth-surfaces-give-surface-subgroups, cckw-kms-triangle-groups-structure]
artifacts:
  - experiments/kms-surface-girth-general/intsearch.py
  - experiments/kms-surface-girth-general/intsearch2.py
  - experiments/kms-surface-girth-general/explore.py
  - experiments/kms-surface-girth-general/cert.py
  - experiments/kms-surface-girth-general/certificates/hbc2-integer-t24-n6.json
  - experiments/kms-surface-girth-general/verify-hbc2-integer-t24-n6.log
  - experiments/kms-surface-girth-general/certificates/hbc2-f5-t24.json
  - experiments/kms-surface-girth-general/verify-hbc2-f5-t24.log
  - experiments/kms-surface-girth-general/verify_modp.py
  - experiments/kms-surface-girth-general/certificates/corrupt-control.json
  - experiments/kms-surface-girth-general/verify-corrupt-control.log
  - experiments/kms-hb2-surface-subgroups/verify_kms_certificates.py
---

## The certificates

- `hbc2-integer-t24-n6.json` was produced on MSI by `intsearch.py HBC2_2 24 6` (job 793895). It enumerates the
  girth surfaces with 24 chambers exactly as `kms_girth_search.py` does, lists the trivial vertex words with
  integer exponents in `[−6, 6] ∖ 0` through `kms-vertex-words-close-iff-weights-have-zero-height-moments` (each
  word re-checked with the normal-form law of `kms_girth_search.word_trivial`), and solves for one label per side.
- `hbc2-f5-t24.json` was produced by `cert.py HBC2_2 24 5 67,5` (job 794384), which solves over `F_5` with vertex
  words evaluated through the normal-form law mod 5.
- Both files use the convention of `kms-girth-surfaces-give-surface-subgroups`: one label `[k, t, s, x]` per side with
  `t < s = r_k(t)`; crossing from `t` to `s` contributes `g_k^x`, and from `s` to `t` contributes `g_k^{−x}`.

## Verification

Both verifiers share no code with the searches.

- `verify_kms_certificates.py` (landed with `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups`) on the integer
  certificate: `verify-hbc2-integer-t24-n6.log` shows ALL PASS for surfaces 67 and 71. For each it checks
  involutions, transitivity, orbit sizes `2m_i`, one nonzero integer label per side, and every vertex word equal to
  `I` over `Z`; it also computes orientability, `V − E + F` and the primes dividing labels, and prints: surface 67
  orientable, `χ = −2`, label primes `{2, 3, 5}`. The models are `U_3`:
  `x ↦ I+E_03+E_12`, `y ↦ I+E_10−E_23`; `U_4`: designated `x ↦ I+E_31`, other `↦ I+E_10−E_23`. For `G_HBC2(2)`
  the designated generators are `b` at `X_1` and `c` at `X_2`.
- `verify_modp.py` on the `F_5` certificate: `verify-hbc2-f5-t24.log` shows ALL PASS for surfaces 67 and 5. It runs
  the same checks with labels in `{1, …, p−1}` and matrix products reduced mod `p`, for the same models.
- *Control.* `corrupt-control.json` changes one label of an `F_7` certificate for surface 65;
  `verify-corrupt-control.log` shows the vertex-word check failing.

## The models are faithful

- *Over `Z`.* The section "The matrix models are faithful on the integral vertex groups" of
  `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups-proof` shows that the models are injective on the normal
  forms of `N_3` and `N_4`, whichever generator is designated.
- *Mod `p`.* Step 0(c),(d) of `kms-hb2-girth-surfaces-give-surface-subgroups-proof` show that the same matrices,
  reduced mod an odd prime `p`, are injective on `U_3(p)` and `U_4(p)`: the listed entries of the symbolic images
  vanish only when all exponents are `0` mod `p`. The designated generator of `U_4(p)` plays the role of `c` there.

So a vertex word that maps to `I` over `Z` is trivial in `N_3` or `N_4`, and a vertex word that maps to `I` mod `p`
is trivial in `U_3(p)` or `U_4(p)`.

## Deduction

- *`p ≥ 7`.* No label of the integer certificate is divisible by `p`. The surjections `N_3 → U_3(p)` and
  `N_4 → U_4(p)` obtained by adding `x^p, y^p` carry the trivial integral vertex words to trivial words in the vertex
  groups `X_0, X_1, X_2` of `G_HBC2(2)(p)`. So surface 67 with these labels, read mod `p`, is a girth surface for
  `G_HBC2(2)(p)` in the sense of `kms-girth-surfaces-give-surface-subgroups`.
- *`p = 5`.* The `F_5` certificate is a girth surface for `G_HBC2(2)(5)` directly.
- In both cases `kms-girth-surfaces-give-surface-subgroups` gives an injective homomorphism `π_1(S) → G_HBC2(2)(p)`
  with quasiconvex image. `S` is orientable with `χ(S) = 24 (1/6 + 1/8 + 1/8 − 1/2) = −2`, so it is the closed
  orientable surface of genus 2.
- Property (T) for `p ≥ 7` is CCKW Corollary 7.8 (`cckw-kms-triangle-groups-structure` item 5). Every finite-index
  subgroup of a group containing a closed surface subgroup `Σ` contains `Σ ∩ H`, a finite-index subgroup of `Σ`,
  which is again a closed surface group.
