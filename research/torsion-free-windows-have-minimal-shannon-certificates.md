---
rg: 2
id: torsion-free-windows-have-minimal-shannon-certificates
kind: claim
title: In a torsion-free group every Bernoulli window configuration is certified by Shannon inequalities on its own window
distinct_from:
  rokhlin-window-transport-is-dominated: that is domination for every group by any proof; this asks for a proof of a fixed local shape, the minimal-window Shannon LP, and only for torsion-free groups.
  minimal-window-shannon-derivations-miss-rokhlin-domination: that shows the local method fails once the group has an element of order 3, 4 or 5; this conjectures that torsion is the only way it fails.
  bernoulli-window-codeword-folner-ratio-bound: that certifies domination with an enlarged window along right Følner sets of <F F^-1>; this asks for no enlargement and no amenability.
artifacts:
  - research/artifacts/shannon-window-certificates-2026-09-17.md
  - experiments/shannon-window-certificates-2026-09-17/shannon_lp.py
  - experiments/shannon-window-certificates-2026-09-17/random_scan.py
---
**OPEN.** Let `G` be torsion-free and `(k, E, F, psi)` a configuration. Put `X = FE ∪ {1}` and `k log q = 1`.
Then the linear program of the artifact, Section 2, has value `>= 1`. The program minimises
`h(y_f0) + h(x_1 y_F) - h(y_F)` over polymatroids on `{x_g : g in X} ∪ {y_f : f in F}` with
- independent unit `x`;
- `y_g` a function of `x_(gE)`;
- translation invariance inside the window.

**Consequence if true.** Every minimal-window LP value is a lower bound for `Phi / log q`. So `Phi >= log q`
for every configuration, and `rho_q(G) = log q` by `bernoulli-rokhlin-deficit-has-a-finitary-witness`. That
is Bernoulli Rokhlin maximality for every torsion-free group, and by
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts` it gives Gottschalk surjunctivity and Kaplansky direct
finiteness for every torsion-free group. This would include the torsion-free nonsofic groups
`integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic` and
`fp-torsion-free-nonsofic-group-of-cd-at-most-three`.

**Each LP value is a finite computation per pattern.** The LP depends only on:
- which elements `p q^-1 s` coincide with window points, for `p, q, s` window points;
- the incidence pattern of `FE`.

So for each finite data set it is one LP.

## Attempts

- **Census (a-gs-rokhlin-obstruction, 2026-09-17).** In 140 distinct configurations the LP value is 1:
  - `F_2`: all 38 with `|E| = 3` and `|F| = 2` in small balls, 9 with `|F| = 3`, and 3 random with at least two readers;
  - `Z`: 27 exhaustive and 7 dense windows up to `|V| = 12`;
  - `Z^2`: 17 random;
  - `H_3(Z)`: 40 random.

  In the same census, 26 of 95 `Z/5` configurations fall below 1, as do cyclic hosts of orders 3, 4 and 7 and `Z × Z/3`. Every fake found
  meets a finite orbit `<t>`. In the four cases tested, adding that orbit's missing codewords restores value 1. The windows of the
  `Z/3`, `Z/4` and `Z/5` fakes, read in `Z`, certify.
- **Limits of the evidence.** All tested hosts are sofic, so domination is already known there, and only small windows
  (`|V| <= 13`) were tested. No mechanism is known that forces LP `>= 1` in torsion-free groups. A plausible proof
  would combine a left order with the chain rule, but not every torsion-free group is left-orderable. A plausible
  failure mode is a finite pattern with a translation cycle that is not a finite orbit, such as a commutation square. The `Z^2` and
  `H_3(Z)` samples contain such squares and still certify.
- **How to refute.** Find a torsion-free pattern with LP `< 1` (`random_scan.py` or `shannon_lp.build` with
  a new group class). A fake alone refutes only this claim, not domination.
