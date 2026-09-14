---
rg: 2
id: finite-actions-with-vanishing-class-norm-make-extension-sofic
kind: claim
title: A finite central extension of a finitely presented residually finite group is sofic when its class has vanishing Hamming norm along finite actions
distinct_from:
  weakly-bernoulli-liftable-action-makes-extension-sofic: that gets soficity from a liftable free action weakly contained in Bernoulli; this gets it from exact finite actions carrying small-support torsor cochains, with no Bernoulli input and no weak containment.
  gohla-thom-stable-base-nonsofic-extension: that is the nonsofic direction for stable bases under a uniform cosystolic lower bound; this is the sofic direction, unconditional on stability.
artifacts:
  - research/artifacts/sk-deligne-sofic-2026-09-14-part1.md
---

**ESTABLISHED** (`finite-action-vanishing-class-norm-sofic-proof`). Unreviewed.

Let `Gamma = <S | R>` be finitely presented and residually finite, `A` finite abelian, and `alpha` the class of a
central extension `1 -> A -> Gamma~ -> Gamma -> 1`. For a finite `Gamma`-set `X`, let `nu_X(alpha)` be the least
normalized number of defective relator cells `(x, r)` of a torsor cochain `b : S x X -> A`: cells whose holonomy differs
from the relator value `a_r` on fixed lifts. If `inf_X nu_X(alpha) = 0`, then `Gamma~` is sofic, through torsor sofic
approximations `V_n x A` over exact finite actions.

Model tests:
- For a split extension `b = 0` has no defect.
- A residually finite `Gamma~` has `nu_X = 0` on a finite quotient.
- For a non-residually-finite `Gamma~`, `nu_X > 0` for every `X`, so only the infimum can vanish.

## Review
- **sk-verify-19 PASS (2026-09-14, `research/artifacts/sk-verify-19-2026-09-14-part2.md` §4):** every step re-derived:
  - amplification by X_n×Γ/N_n (defect fraction unchanged; normality makes g ∉ N_n move every point);
  - exact A-relations and commutators, with r = a_r at (v,t) iff the cell (v,r) is not defective;
  - discrete Stokes on van Kampen diagrams of radius C_w (A abelian), bad fraction ≤ |B_{C_w}||R|ν_n;
  - nontrivial central a moves the good points.
  - Model tests (split, residually finite, non-residually-finite) are consistent.
