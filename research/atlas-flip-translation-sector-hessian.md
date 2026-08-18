---
rg: 2
id: atlas-flip-translation-sector-hessian
kind: claim
title: Exact second-order verdict on the translation sector — no escape, and the active slice is flat there too
distinct_from:
  atlas-flip-first-order-rigidity: that is the exact FIRST derivative (zero everywhere, proved); this is the exact SECOND derivative on the structured sector — nonnegative loss curvature on 8,600 directions with the active slice contributing exactly nothing.
  atlas-stabilizer-commutant-no-go: that kills stabilizer-commuting deformations by a positive lower bound at all orders; this is a curvature computation at one point on a different (translation-algebra) sector, and neither statement contains the other.
artifacts:
  - research/artifacts/atlas-flip-hessian-scan-2026-08-18.json
  - research/artifacts/atlas-true-criterion-probe-2026-08-15.md
  - experiments/atlas_flip_hessian_scan.py
---

At the flip the gradient is exactly zero (`atlas-flip-first-order-rigidity`),
so the Riemannian Hessian of the stage-2 objective is the plain second
derivative.  Every Hessian term of a `T_St` word reduces by cyclicity to
canonical forms `tr(X T₂ X T₁)` and `tr(X² T)` with translation contexts,
and on the structured anti-Hermitian directions

```text
E(u,v) = L_u R_v − L_{u⁻¹} R_{v⁻¹},    E′(u,v) = i(L_u R_v + L_{u⁻¹} R_{v⁻¹})
```

it evaluates in exact integers by fixed-point counts.  The engine passed a
300-check end-to-end self-test against dense-matrix computation over `S₄`
(both families, random mixed words; zero failures).

**Result 1 (exact, 8,000 evaluations): no second-order escape in the
sector.**  Over 4,000 catalog pairs `(u, v)` (letter-generated, closed
under products of two, gauge directions excluded) × both families, with
the full active set and a 72-word control sample: **zero directions of
negative loss curvature**.  `max Q_total = 0`, attained on flat
directions; everywhere else the loss curves strictly upward
(`Q_control` as negative as `−1.7 × 10⁷`).

**Result 2 (exact, 8,600 evaluations): the active slice is Hessian-flat
on the sector.**  `Q_active = 0` on every direction of the scan AND on
600 fresh directions from an independent seed, tested per class: both
the 36 `p₁`-trivial and the 36 `p₂`-trivial escapees vanish separately.
All second-order resistance in the sector comes from the control words.
Observed mechanism candidate for a future proof: for `p₁`-trivial words
the cross terms' `L`-parts pair as `(b, b⁻¹)` (`b` the between-sites
`K1` product), the second-order shadow of the first-order telescope.
Conjecture, unproved: the active Hessian form vanishes identically on
the whole translation sector (the verification covers the diagonal of
the form on sampled directions; polarization/cross terms untested).

**Result 3 (dense counterexample): no global flatness.**  In the `S₄`
model the active-type trace `tr(L_g W R_a W* L_{g⁻¹} W R_b W*)` is
NONZERO for random unitary `W` (order-one values; zero exactly at
`W = I`).  So the local flatness does not extend to an algebraic
identity in `W`: the active defects can in principle move under large
unstructured deformations, and the criterion at large `k` stays
genuinely open — this fence kills any temptation to read the local
results as a `k = 1` impossibility theorem.

**Combined landscape statement.**  At the flip: first order exactly
zero everywhere (theorem); second order on the translation sector
exactly nonnegative for the loss, with the active slice contributing
nothing (8,600 exact evaluations); unstructured directions empirically
nonnegative (the completed V100 run equilibrated above baseline with
zero descent).  Everything consistent with a local minimum whose
resistance is carried entirely by the satisfied relators; nothing here
selects a branch of `leavitt-steinberg-hs-unstable`.  Sharper
instruments if resumed: polarization of the form (sums of pairs),
subspaces beyond the translation sector, and plain-SGD/momentum
dynamics for the unstructured part.
