---
rg: 2
title: All-relator evaluation of the d = 20, 30, 40 seeded descents in the mod-three Maslov sector of Sp4(Z) (2026-09-13)
kind: artifact
---

# Status

Numerics only. This completes Section 3 of
`research/artifacts/sp4-twist-defect-numerics-2026-09-13.md`, whose all-relator table was pending.
- Every number is an upper bound on least relator defects over the length-13 root window.
- Nothing here is a lower bound.
- Nothing here is evidence for or against non-hyperlinearity of any group, or for or against
  `maslov-mod3-projective-defect-gap`.
- No node status changes because of this file.

# Run

MSI job `721130` (`nh-evalall`, COMPLETED, 00:04:50), work directory
`/projects/standard/hsiehph/sauer354/nhnum`, script `eval_descent_all.py`.
- **md5s:** `eval_descent_all.py` c5b8cc3eaa3a5924c9236a6d5912d261; `pres6.json`
  3b6b79835437ee157005e7fa65cd3671; `seed_theta_d10.json` da7d9eb2d9ada1eefad991df4ab90e30.
- **Product convention.** The evaluator requires the exact `d = 10` metaplectic seed to give
  `(-1)^(k_r) I` on every relator. "Order left" gives `0.000e+00`; "order right" gives `1.549e+00`.
  So "order left" is used.
- **Relators:** all `304,412` (all `304,392` unlifted plus the `20` lifted ones), normalized HS,
  target `omega^(k_r) I`.

# All-relator table

`start` is the stacked coboundary start point (old `0.309` phases); `min` is the saved descent minimum
from job `709526`.

```text
d   point   max unlifted  max lifted  max      mean sq   q50     q99     q999    #> bar 0.306783
20  start   0.3091        0.3071      0.3091   0.006382  0.0603  0.1870  0.2469  30
20  min     0.3221        0.3204      0.3221   0.006387  0.0598  0.1940  0.2548  24
30  start   0.3091        0.3071      0.3091   0.006382  0.0603  0.1870  0.2469  30
30  min     0.3249        0.2793      0.3249   0.006917  0.0629  0.1961  0.2594  46
40  start   0.3091        0.3071      0.3091   0.006382  0.0603  0.1870  0.2469  30
40  min     0.3400        0.2621      0.3400   0.007399  0.0652  0.2061  0.2720  46
```

- **Worst relators.** All worst relators are unlifted and of length `12`. For example, `d = 40` min:
  `(300587, 12, 0, 0.34)`, `(299716, 12, 0, 0.34)`, `(299642, 12, 0, 0.34)`.
- **Phases.** At every minimum the generator phases (divided by `2 pi`) stay about `-0.010` on letters
  `0, 1` and `+0.010` on letters `4, 5`, as at the start. The nonabelian residual per generator is
  about `0.017` to `0.019`.

# Reading

1. **The sub-bar working-set values were sampling artifacts.** The working-set maxima `0.2793`
   (`d = 30`) and `0.2757` (`d = 40`) became `0.3249` and `0.3400` on all relators. Every descent
   minimum is above the exact abelian bar `2 sin(5 pi / 102) = 0.306783` and above its own start point
   `0.3091`.
2. **No nonabelian valley was found, and no dimension dependence.** The lifted relators improved
   (`0.3071 -> 0.2621`), but only by pushing unlifted length-12 relators up. The minima get *worse*
   with `d` at this fixed iteration budget.
3. **Blind instrument.** `maslov-bounded-block-sector-gap` forces any vanishing-defect sequence to carry
   asymptotically all mass in irreducible blocks of unbounded size. Local descent from stacked exact
   seeds in `d <= 40` stays near block size `10`. So this completes the record of that instrument; it
   says nothing about the open premise.

# Files

The log `evalall.721130.log` and the three `.npy` minima stay on MSI in the work directory above. They
were not copied here: the MSI connection was down when this artifact was written.
