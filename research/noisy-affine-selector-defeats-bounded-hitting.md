---
rg: 2
id: noisy-affine-selector-defeats-bounded-hitting
kind: claim
title: A folded Boolean direction decoder has noisy heavy affine cosets with no bounded hitting list
artifacts:
  - research/artifacts/unique-games-noisy-direction-counterexample-2026-09-07.md
  - scripts/check_unique_games_noisy_direction.py
  - research/artifacts/unique-games-noisy-direction-replay-2026-09-07.json
---

For every fixed `0<rho<1` and all sufficiently large `N=4^m`, there is
a folded Boolean function `f_N` on `{-1,1}^{F_2^(2m)}` and a selected
coset `C_b` for every nonzero direction such that

```text
Inf_C_b^{<=1}((T_rho f_N)|D_b) >= rho^2/4,
|{b : C_b intersects Q}| <= 2|Q|                  for every Q,
Pr_(b,c uniform nonzero)[C_b intersects C_c] = 3/(N-1).
```

Take `J(a,b)=(b,a+b)` on each binary coordinate pair and
`C_b={Jb,J^2b}`. The function outputs `Y_(J bhat(Y))`, where `bhat`
maximizes the pair autocorrelation of its input, with deterministic ties.
It is bounded and folded on the entire ambient cube, not merely on the
restricted cubes. Noise is applied in the ambient cube before restriction.

For `rho=1/2`, all `N=4^m>=16384` suffice. This fixes
`d=1,delta=1/16,alpha=1/2` while any `L` labels hit at most `2L/(N-1)` of
the directions. It refutes both `affine-orientation-glue-lemma` and
`affine-orientation-triangle-defect-is-small`. It does not refute UGC,
the Rich 2-to-1 conjecture, or the established quadratic special case.

The complete proof is in the artifact. Exact finite replays validate the
implementation and normalizations; they are not the universal proof and
are not Lean verification.
