---
rg: 2
id: torsion-free-windows-have-minimal-shannon-certificates
kind: claim
title: In a torsion-free group every Bernoulli window configuration is certified by Shannon inequalities on its own window
distinct_from:
  rokhlin-window-transport-is-dominated: that is domination for every group by any proof; this asks for a proof of a fixed local shape, the minimal-window Shannon LP, and only for torsion-free groups.
  minimal-window-shannon-derivations-miss-rokhlin-domination: that shows the local method fails once the group has an element of order 3, 4 or 5; this conjectures that torsion is the only way it fails.
  bernoulli-window-codeword-folner-ratio-bound: that certifies domination with an enlarged window along right Følner sets of <F F^-1>; this asks for no enlargement and no amenability.
  shannon-window-fakes-on-klein-and-infinite-dihedral-hosts: that extends the torsion fakes to (Z/2)^2, D_inf and order 7; this conjectures their absence without torsion.
artifacts:
  - research/artifacts/shannon-window-certificates-2026-09-17.md
  - research/artifacts/shannon-window-fakes-on-involution-hosts-2026-09-17.md
  - experiments/promislow-shannon-windows-2026-09-17/hw_scan.py
  - experiments/promislow-shannon-windows-2026-09-17/rs_hw_seed7.txt
  - experiments/shannon-window-certificates-2026-09-17/shannon_lp.py
  - experiments/shannon-window-certificates-2026-09-17/random_scan.py
  - experiments/shannon-kemperman-2026-09-17/kemperman_census.py
  - experiments/torsion-free-structured-windows-2026-09-17/box_scan.py
  - experiments/torsion-free-structured-windows-2026-09-17/scan_z2_43.txt
  - experiments/torsion-free-structured-windows-2026-09-17/scan_free_33.txt
  - experiments/torsion-free-structured-windows-2026-09-17/scan_heis_33.txt
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
- **Hostile torsion-free host and order-2 torsion (swarm-0917-w3-gs-pull-1, 2026-09-17).** Artifact
  `research/artifacts/shannon-window-fakes-on-involution-hosts-2026-09-17.md`.
  - *Promislow / Hantzsche–Wendt group* `P`: torsion-free, not left-orderable, no unique products. In 150 random configurations (`n <= 12`, at least 2 readers), the LP value is exactly 1 (`hw_scan.py`, `rs_hw_seed7.txt`). So the two obvious proof mechanisms, a left order or unique products, are not what makes the evidence hold.
  - *Dense Z.* `E = {0..m-1}`, `F = {0,...,-(m-1)}` gives LP 1 at `m = 4` (`n = 11`) and `m = 5` (`n = 14`) (`dense_z_large.txt`). The Følner-loss heuristic, that dense windows get harder, does not show up at this size.
  - *Unique products are not the invariant.* Some fakes are UP pairs: `Z/5` with `E = {0,1,2}`, `F = {0,2,4}` at 0.916667, 2 of 6 in `Z/7`, and all 6 in `Z × Z/3` (`up_census.txt`). A proof cannot go through unique products inside the window.
  - *Order-2 torsion does kill the method.* There are exact fakes on `(Z/2)^2` (7/9), `D_inf` (7/8) and `Z/7` (5/6); see `shannon-window-fakes-on-klein-and-infinite-dihedral-hosts`. `D_inf` contains `Z` with index 2, and every tested `Z` window certifies. So a proof cannot use only virtual torsion-freeness; it has to use torsion-freeness of the whole group. (Referees flagged that the tested census does not show that `Z` certifies every window.)
  - *Sharper frontier.* Among groups with torsion, fakes are known in every group except where every finite order is `m` or `2m` with the prime factors of `m` at least 11, and any two distinct involutions have a product of odd order. `Z × Z/2` shows no fake in 418 configurations: 338 exhaustive in the box `[-1,1] × Z/2` with `n <= 11`, and 80 random. A partial `Z/11` shape scan also shows none: 21 of 56 classes (`cps_z11.txt`). So the correct statement might be broader than torsion-free, and `Z × Z/2` is the test case.
  - *Still open.* No mechanism is known. All hosts are sofic, and `n <= 14`.
- **Rank-condition prerequisite (swarm-0917-w4-pull-gs-1, 2026-09-17).** `window-shannon-certificates-force-rank-condition` (ESTABLISHED):
  - a twisted linear profile over any field crossed product `K*N`, restricted to a finite window, is a feasible point of this LP with the same `Phi`;
  - rank-condition failure passes to finite-index subgroups through `K*H ⊂ M_n(K*N)`;
  - so this claim implies **(RC-vtf)**: every field crossed product over a group whose finitely generated subgroups are virtually torsion-free has the rank condition. This includes all finitely generated linear groups in characteristic 0;
  - any witness of `some-field-crossed-product-fails-the-rank-condition` over such a group refutes this claim. Next test cases: `Q(x,y) ⋊ SL_3(Z)`, `F_p(x_g) ⋊ Γ` for Kazhdan lattices;
  - by `virtually-hughes-free-field-crossed-products-are-stably-finite`, (RC-vtf) can fail only on groups outside the virtual Hughes-free class. Every host in the census is inside that class, so the census never tests this failure mode.
- **Sumset census (swarm-0917-w4-pull-gs-1).** `experiments/shannon-kemperman-2026-09-17/kemperman_census.py`, over the cyclic census files:
  - every fake has `|FE| <= |E| + |F| - 1`, and none is above the Kemperman bound that torsion-free groups obey;
  - fakes at equality occur in `Z/5` and `Z/7`;
  - the invariant is not hereditary strict saturation: `Z/5`, `E = {0,1,2}`, `F = {0,2,4}` is a fake without a strictly saturated sub-pair;
  - in `Z × Z/5`, adding a far element to `E` keeps a fake with `|FE| >= |E| + |F|`. So "large sumset forces certification" fails once torsion is present, and a Kemperman-type route would have to use torsion-freeness beyond the sumset size.
- **Exhaustive dense radius-1 census (swarm-0917-w18c-w18c-gs-pull, 2026-09-19).** Evidence only; the claim stays OPEN.
  Script: `experiments/torsion-free-structured-windows-2026-09-17/box_scan.py`. It solves every configuration with at
  least two readers of `x_1` and ground set `n <= 13`. All 524 solves return status 0 with LP value exactly `1`. There is no fake.
  - `Z^2`, with `E`, `F` in the box `[-1,1]^2`, both containing `0`, deduplicated by `(E+g, F-g)` and the 8 lattice
    symmetries:
    - `|E|,|F| = 3,2`: 7 configurations;
    - `3,3`: 44;
    - `4,2`: 23;
    - `4,3`: 120, i.e. every class with `n <= 13`.

    These include the 2x2 box `E = -F` (4 readers, `n = 13`) and every triangle cycle `a + b + (-a-b) = 0`.
  - `F_3`, with `E`, `F` in the radius-1 ball, both containing `1`: all 135 configurations at `3,3` and all 60 at `4,2`.
  - `H_3(Z)`, with the ball `{x^±1, y^±1, z^±1}`: all 135 at `3,3`. Commutator coincidences `xy = yxz` occur here.
  - Output files are `scan_*.txt`.
  - Earlier censuses were random, or used `|F| <= 2`. This is the first exhaustive census of dense windows with 3 to 4 readers in `Z^2`,
    `F_3` and `H_3`.
- **Where the known two-reader fakes come from (same agent).** Of the 15 fakes with `|F| = 2` in
  `experiments/shannon-canonical-hosts-2026-09-17/recheck_all.txt`, I checked 14 by hand. In each, `E` contains a
  coset of the finite cyclic group generated by the reader ratio `t = f^-1 f'`. So `fE` and `f'E` share a
  `t`-invariant block. The hosts are `Z/3`, `Z/4`, `Z/6`, `S_3` and Heisenberg mod 3. In a torsion-free group no
  finite nonempty set is `t`-invariant for `t != 1`, so this mechanism is unavailable there.
  - I have **no proof** that this is the only way a two-reader fake can arise. The obvious chain-rule attempt,
    conditioning on `x_((W1 ∪ W2) \ 1)`, gives `Phi >= 1 + H(y) - H(y_1 y_2 | x_rest)`. That is the wrong direction, and
    it dies there.
  - `reader_only_lp.py` (`reader_only.txt`) imposes `(T)` only for reader ratios `f f'^-1`. On the 8 test cases it
    returns the same values as the full LP. This is uninformative, because in these windows almost every
    translation `p q^-1` is already a reader ratio.
