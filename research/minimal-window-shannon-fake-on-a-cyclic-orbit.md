---
rg: 2
id: minimal-window-shannon-fake-on-a-cyclic-orbit
kind: route
title: Exhibit an exact translation-invariant polymatroid on the Z/3 window with Phi equal to five sixths
target: minimal-window-shannon-derivations-miss-rokhlin-domination
requires: []
artifacts:
  - research/artifacts/shannon-window-certificates-2026-09-17.md
  - experiments/shannon-window-certificates-2026-09-17/verify_fake.py
---
Artifact Sections 2 and 4.

1. **Reduction to `Z/3`.** For `E = {1,t,t^2}` and `F = {1,t}`:
   - all sites lie in `<t>`, so `X = <t>`;
   - every translation `s' s^-1` between sites lies in `<t>`;
   - a translation carrying a nonempty subset of the window into the window is of this form.

   So the premises (P), (I), (D), (T) are the same in `G` as in `Z/3`.
2. **The fake.** Artifact Section 4 lists `h` on all 31 nonempty subsets of `{x0, x1, x2, y0, y1}`. The verification checks exactly:
   - `h(empty) = 0`;
   - the 5 top monotonicity inequalities and the 80 elemental submodular inequalities;
   - `h(x_i) = 1` and `h(x0 x1 x2) = 3`;
   - `h(y_g x0 x1 x2) = h(x0 x1 x2)`;
   - the 32 translation equalities under `t = +1, +2`.

   Elemental inequalities imply all Shannon inequalities, so `h` satisfies every premise, and
   `Phi = 5/6 + 5/3 - 5/3 = 5/6`.
3. **LP duality.** Any derivation of `Phi >= 1` from the premises is a nonnegative combination of
   premise (in)equalities. Evaluated at `h`, it would give `5/6 >= 1`.
4. **Orders 4 and 5.** The same exact checks run on the configurations with values `7/9` (679 elemental
   inequalities, 192 translation equalities) and `4/5` (1800 and 384).

Reproduce with the following commands. Each exits `0` and prints `ALL EXACT`:

    python3 experiments/shannon-window-certificates-2026-09-17/verify_fake.py 3 0,1,2 0,1
    python3 experiments/shannon-window-certificates-2026-09-17/verify_fake.py 4 0,1,2,3 0,1,2
    python3 experiments/shannon-window-certificates-2026-09-17/verify_fake.py 5 0,1,2,4 1,2,3

These must be run from inside `experiments/shannon-window-certificates-2026-09-17/`, because the scripts import `shannon_lp` and `random_scan` from that directory.
