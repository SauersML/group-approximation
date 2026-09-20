---
rg: 2
id: thompson-f-census-witnesses-have-frozen-trace-spread
kind: claim
title: The best fixed-threshold census witnesses for Thompson's F are diluted negative-trace cores whose trace spread on short F' words does not shrink
distinct_from:
  thompson-f-trace-spread-caps-the-census-ratio: that is the theorem that spread caps the ratio; this is the float64 measurement placing the known census witnesses in a capped family.
  thompson-f-commutator-bound-holds-in-each-fixed-dimension: that proves lower bounds on C_n from explicit small pairs; this dissects the large-n optimizer witnesses and shows that their ratio growth is not evidence about sup C_n.
artifacts:
  - research/artifacts/thompson-f-census-trace-spread-2026-09-17.md
  - experiments/thompson-f-witness-trace-test-2026-09-17/profiles_S8.out
  - experiments/thompson-f-witness-trace-test-2026-09-17/blocks_n16.out
  - experiments/thompson-f-witness-trace-test-2026-09-17/blocks_n32.out
  - experiments/thompson-f-witness-trace-test-2026-09-17/blocks_n64.out
  - experiments/thompson-f-witness-trace-test-2026-09-17/blocks_n64b.out
  - experiments/thompson-f-witness-trace-test-2026-09-17/impose.out
  - experiments/thompson-f-witness-trace-test-2026-09-17/check_classes.out
---

**Statement** (float64 computation on the listed files). The fixed-threshold census at `tau = 1.8` has certified
witnesses with ratio `e(c)/max_i e(R_i)` of 12.51, 15.91, 17.94 and 20.16 at `n = 16, 32, 64, 128`. These are from the
w19 defect-profile run, commit `3d20450385`, and are copied as `wit_F_n*.npy`.

1. **Frozen spread.** Let `S_8` be the 17 classes of nontrivial `F'` words of length at most 8, checked exactly
   in PL arithmetic. Each witness has `max over S_8 of |tr w - tr c|` in `[0.396, 0.553]`, with no downward trend in `n`.
   So `sigma_{S_8} >= 0.19` on the whole family. For comparison, every character of `F` has spread 0 on `S_8`.
2. **Diluted cores.** To leakage at most 0.014, the witnesses split so far are each a direct sum of one core and
   commuting scalar pairs. These are `n = 16`, `n = 32`, the certified `n = 64b` and an uncertified `n = 64`
   witness, with cores of 12, 23, 50 and 45 dimensions.
   - The core carries the whole ratio: 12.60, 15.91, 17.97 and 15.88.
   - Each core has `e(c)` between 2.40 and 2.56, that is, `Re tr c` between -0.20 and -0.28. No character of `F`
     allows a negative value on `c`.
3. **Cost of consistency.** Restart from the same certified witnesses and require `e(w) >= 1.8` on all of `S_8`
   instead of on `c` alone. The reached ratio drops as follows:

   | n | `c` alone | all of `S_8` |
   |---|---|---|
   | 16 | 15.75 | 6.78 |
   | 32 | 15.81 | 7.11 |
   | 64 | 17.25 | 7.22 |

**Consequence.** Item 1 and `thompson-f-trace-spread-caps-the-census-ratio` together show that the ratio ladder
12.5 to 20.2 lies in a family whose ratio is bounded by `4/delta(S_8, 0.19)` in every dimension. It is therefore
not evidence that `sup_n C_n(F) = infinity`, and it is not evidence against it either. Census evidence about
hyperlinearity of `F` must come from witnesses with `sigma_S -> 0`. That constrained census is open.

Derivation: `thompson-f-census-witnesses-have-frozen-trace-spread-computation`.
