---
rg: 2
id: minimal-window-shannon-derivations-miss-rokhlin-domination
kind: claim
title: Shannon inequalities on a configuration's own window do not prove Rokhlin window domination in any group with an element of order 3, 4 or 5
distinct_from:
  rokhlin-window-transport-is-dominated: that is the domination inequality itself, still open; this kills one proof method for it, on configurations where the inequality is true.
  cancellative-incidence-patterns-do-not-force-domination: that is a genuine low-Phi code on an incidence pattern no group realizes; this is a fake entropy vector on a pattern realized in Z/3, where domination holds but is not derivable on the window.
  bernoulli-window-codeword-folner-ratio-bound: that is a Shannon derivation on the enlarged window x on SFE, y on SF; this shows the enlargement is necessary.
artifacts:
  - research/artifacts/shannon-window-certificates-2026-09-17.md
  - experiments/shannon-window-certificates-2026-09-17/verify_fake.py
  - experiments/shannon-window-certificates-2026-09-17/shannon_lp.py
---
**ESTABLISHED** (route `minimal-window-shannon-fake-on-a-cyclic-orbit`).

**Setup.** Let `G` be a group and `(k, E, F, psi)` a configuration with `1 in E`, `X = FE ∪ {1}` and
`k log q = 1`. The *minimal-window Shannon method* derives `Phi >= 1` from:
- all Shannon inequalities among the variables `{x_g : g in X} ∪ {y_f : f in F}`;
- independence and normalisation of the `x_g`;
- the functional dependencies `y_g = psi(x_(gE))`;
- the translation equalities `H(S) = H(tS)` for all `S`, `tS` inside the window.

It succeeds on a configuration iff the linear program of the artifact, Section 2, has value `>= 1`.

**Claim.** Let `t in G` have order `3`, and take `E = {1, t, t^2}`, `F = {1, t}`. Then some polymatroid on the
five variables `x_1, x_t, x_(t^2), y_1, y_t` satisfies every premise of the method and has

    Phi = h(y_1) + h(x_1 y_1 y_t) - h(y_1 y_t) = 5/6 < 1 .

So the method fails on this configuration, in every group with an element of order 3. The same holds with value `7/9` for
`t` of order 4, `E = <t>` and `F = {1, t, t^2}`, and with value `4/5` for `t` of order 5, `E = {1,t,t^2,t^4}` and `F = {t,t^2,t^3}`.

**The inequality is true there.** `<F F^-1>` is finite, so `lambda(F) = 1` and `Phi >= log q` by
`bernoulli-window-codeword-folner-ratio-bound`. The failure is a failure of the method, not a deficit.
Adding the single missing codeword `y_(t^2)` (all of `<t>`) restores LP value `1`.

**What dies.** The class is every argument for `rokhlin-window-transport-is-dominated` that works one
configuration at a time and uses only linear information inequalities of Shannon type on the variables of
that configuration's window: per-term transport bounds, sunflower-type conditional independence, and
the random-order chain rule truncated to `y_F`. Every member dies at the final step, the nonnegative combination
of elemental inequalities: the exact polymatroids above satisfy all premises and violate the conclusion.
A surviving proof must use either:
- codewords outside `F`, as the Følner count does; or
- non-Shannon inequalities (not tested); or
- information that is not linear in entropies.
