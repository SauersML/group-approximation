# Two-adic tower probe protocol (designed 2026-08-21)

Target: the finite-level closure question of
`two-adic-tower-format-of-surviving-lambda-exact-enemy` — does the
S3-interlocked depth-shifting system admit asymptotic closure over
towers of genuine `SL_3(Z/2^a)` representations with regular trace
profile?

## Why single levels are vacuous

At one fixed level `a`, the intertwining condition constrains `V`
only through the level-dropped reductions (the corner entry loses two
levels), so small-`a` feasibility says nothing: the content is the
MODULUS across the tower — exactly as in Dogon–Vigdorovich Question
1.4, which is a modulus question, not a single-level question.  The
probe must therefore measure the defect floor as a FUNCTION of `a`
and of trace-regularity pressure.

## Design

- Representations: `sigma_a` = permutation representation of
  `G_a = SL_3(Z/2^a)` on `G_a / C_a` where `C_a` is the full preimage
  of a fixed level-4 parahoric intersected with the level-`2^a`
  congruence structure needed for faithfulness; sizes grow by `2^8`
  per level, so work per-block: parametrize `V` in the isotypic block
  structure of `Res_{P_-} sigma_a` (the intertwining condition is
  block-sparse: it couples only blocks matched by the level-dropped
  `Ad(h)`).
- Variables: `V_a` block-unitary; its Weyl conjugates are DERIVED
  (`V_(h') = sigma(w_12) V sigma(w_12)^(-1)` etc.), not independent.
- Defect functional (all normalized HS):
  `delta(V) = max(intertwining defect over Lambda_- generators,
  three-term defect ||V V_(h'')^(-1) - V_(h')||, inversion defect
  ||w_13-conj(V) - V^(-1)||, commutation defects of the tuple)`,
  plus the Haar pressure `H(V) = max_{1<=m<=M} |tr V^m|` and the
  mixed-word regularity residual `R(V)` over a fixed short word list
  (words with one and two h-blocks against Lambda generators, the
  psi-profile words first — target values from the regular trace of
  Gamma, i.e. 0 off the trivial word).
- Protocol: for `a = 2, 3, 4`, minimize
  `delta + beta (H + R)` (strong `beta`), several restarts, polar
  retraction, Armijo (reuse the machinery of
  `experiments/hecke42_average_probe.py` — its optimizer is
  validated; the QR-phase-jump and unit-step traps are already
  fixed there).  Record the Pareto floor
  `delta*(a, beta)`.
- Interpretation: `delta*(a) -> 0` with `H, R -> 0` = structured
  candidate enemy tower (hand to the graph; test against `43/168`
  and the two-block moment constraints before believing).  A floor
  bounded away from `0`, stable or growing in `a`, = quantitative
  evidence for closure of the whole Lambda-exact sector, and the
  floor's `a`-profile estimates the modulus that a proof must
  produce.

## Compute notes

MSI lane only (sioux; `module load python/3.10.10-gcc-8.2.0-sanagub`,
numpy 1.23; probes live at `$HOME/probes/`).  Do not use dense
`U(d)` descent above `d ~ 10^3`; the block parametrization is
mandatory from level 8 up.  Thread caps 4-8; no tmpfs storage.
