---
rg: 2
id: kms-hc1-genus-two-surface-subgroups-proof
kind: route
title: An integer-labelled 48-chamber girth surface verified in faithful integral models is a girth surface for G_HC2(1)(p) at every prime p >= 5
target: kms-hc1-groups-contain-genus-two-surface-subgroups
requires: [kms-girth-surfaces-give-surface-subgroups, cckw-kms-triangle-groups-structure]
artifacts:
  - experiments/kms-surface-girth-general/intsearch2.py
  - experiments/kms-surface-girth-general/intsearch.py
  - experiments/kms-surface-girth-general/certificates/hc1-integer-t48-n4.json
  - experiments/kms-surface-girth-general/verify-hc1-integer-t48-n4.log
  - experiments/kms-surface-girth-general/logs/int-hc1-t48-n4.log
  - experiments/kms-hb2-surface-subgroups/verify_kms_certificates.py
---

## The certificate

`hc1-integer-t48-n4.json` was produced on MSI by `intsearch2.py HC2_1 48 4 all` (job 794523,
`logs/int-hc1-t48-n4.log`).
- It enumerates all 191 girth surfaces with 48 chambers for half girth type `(3,3,4)` with the enumerator of
  `kms_girth_search.py`.
- It lists the trivial vertex words with integer exponents in `[−4, 4] ∖ 0` through
  `kms-vertex-words-close-iff-weights-have-zero-height-moments`, re-checking each with the normal-form law.
- It solves for one label per side. Surface 190 is the only one with a solution.

The file uses the convention of `kms-girth-surfaces-give-surface-subgroups`: one label `[k, t, s, x]` per side, with
`t < s = r_k(t)`.

## Verification

`verify_kms_certificates.py` (landed with `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups`; it shares no code
with the search) gives ALL PASS (`verify-hc1-integer-t48-n4.log`). It checks:
- involutions, transitivity and orbit sizes `2m_i = 6, 6, 8`;
- one nonzero integer label per side;
- every vertex word equals `I` over `Z` in the models `U_3`: `x ↦ I+E_03+E_12`, `y ↦ I+E_10−E_23`; `U_4`: designated
  `x ↦ I+E_31`, other `↦ I+E_10−E_23`. For `G_HC2(1)` the vertices `X_0` and `X_1` are `U_3`, and `X_2 = <a,c>` is
  `U_4` with `x = a`.

It also computes and prints: orientable, `χ = −2`, label primes `{2, 3}`.

## Deduction

- *Faithfulness over `Z`.* The section "The matrix models are faithful on the integral vertex groups" of
  `kms-hc2-hb3-hbc3-contain-genus-two-surface-subgroups-proof` shows the models are injective on the normal forms of
  `N_3` and `N_4`, whichever generator is designated. So every vertex word of the certificate is trivial in the
  integral vertex groups.
- *Every `p ≥ 5`.* No label is divisible by `p`. Adding `x^p, y^p` gives surjections onto `U_3(p)` and `U_4(p)`,
  the vertex groups of `G_HC2(1)(p)`, so the vertex words stay trivial. Surface 190 with the labels read mod `p` is
  a girth surface for `G_HC2(1)(p)`.
- `kms-girth-surfaces-give-surface-subgroups` gives an injective homomorphism `π_1(S) → G_HC2(1)(p)` with
  quasiconvex image, where `χ(S) = 48 (1/6 + 1/6 + 1/8 − 1/2) = −2` and `S` is orientable, so `S` is the closed
  orientable surface of genus 2.
- Property (T) for `p ≥ 7` is CCKW Corollary 7.8 (`cckw-kms-triangle-groups-structure` item 5). A closed surface
  subgroup `Σ` meets every finite-index subgroup `H` in a finite-index subgroup of `Σ`, again a closed surface group.
