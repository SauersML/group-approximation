# Minimal-window Shannon fakes on involution hosts, and torsion-free stress tests (2026-09-17)

Agent `swarm-0917-w3-gs-pull-1`, wave `swarm-0917`, lane obstruction-miner, family entropy-measure.
Target hole: `every-group-has-positive-rokhlin-entropy-action`, through `rokhlin-window-transport-is-dominated`.
This continues `research/artifacts/shannon-window-certificates-2026-09-17.md`; its Section 2 defines the LP.

Code and raw outputs: `experiments/promislow-shannon-windows-2026-09-17/`. The scripts import
`shannon_lp.py` and `random_scan.py` from `experiments/shannon-window-certificates-2026-09-17/`.

## 1. Question

`minimal-window-shannon-derivations-miss-rokhlin-domination` kills the minimal-window Shannon method in
every group with an element of order 3, 4 or 5. The earlier census found no fake at order 2 (3 patterns in `Z/2`),
and conjectured (`torsion-free-windows-have-minimal-shannon-certificates`) that torsion is the only way the method fails.
This artifact answers three questions:
- Which torsion really kills the method?
- Is there a single invariant, such as unique products, that predicts the fakes?
- Does the torsion-free evidence survive a hostile torsion-free host, one that is neither left-orderable nor has unique products?

## 2. Torsion reduction

Every group with torsion contains an element of prime order. An element of odd prime order `p` gives `Z/p`.
If there are no such elements, all torsion has 2-power order, and there are three cases:
1. Some element has order 4. Then `G ⊇ Z/4`.
2. Otherwise all torsion elements are involutions. Two distinct involutions `s, s'` generate a dihedral group of order `2n`, with `n = ord(ss')`:
   - `n = 2` gives `(Z/2)^2`;
   - `n = infinity` gives `D_inf`;
   - `n = 2^k` with `k >= 2` gives `Z/4`, which is excluded here.
3. Otherwise there is exactly one involution `s`. It is central, because each of its conjugates is an involution. If `G` has an element `g` of infinite order, then `<g, s> = Z × Z/2`, since `s` is not in `<g>`. Otherwise every element has order 1 or 2, so `G` is abelian of exponent 2 with a unique involution, which means `G = Z/2`.

So the order-2 test hosts are `(Z/2)^2`, `D_inf` and `Z × Z/2`. The minimal-window LP of `(E, F)` inside a subgroup `H`
is the same LP in every `G ⊇ H`, because all sites and all translations `p q^-1` between sites lie in `H`.

## 3. Exact fakes (`verify_all.sh`, log `verify_log.txt`)

`verify_generic.py GROUP E F [maxden]` works for any group class. It takes a dual-simplex vertex and rationalises it with `limit_denominator(maxden)`.
It then rebuilds `h` on all `2^n` subsets and checks exactly:
- `h(empty) = 0`;
- every elemental inequality;
- (I) `h(x_g) = 1` and `h(x_X) = |X|`;
- (D);
- (T) for every `t = p q^-1` and every subset `S` whose image is in the ground set.

It exits 0 iff every check passes and `Phi < 1`.

| host | E | F | n | elemental | translation | exact Phi |
|---|---|---|---|---|---|---|
| `(Z/2)^2` | `{00,10,01,11}` | `{00,11,01}` | 7 | 679 | 316 | **7/9** |
| `(Z/2)^2` | `{00,10,11}` | `{11,10,01}` | 7 | 679 | 316 | **11/12** |
| `D_inf` | `{1, r0, r1, t}` | `{r1, t^-1, 1, t}` | 12 | 67596 | 6242 | **7/8** |
| `Z/7` | `{0,1,2,4}` | `{0,3,5,6}` | 11 | 28171 | 5113 | **5/6** |
| `Z/7` | `{0,1,2,5}` | `{0,1,2,5}` | 11 | 28171 | 5113 | **1264/1469** |

For `D_inf`, `r0: x -> -x`, `r1: x -> 1 - x` and `t = r1 r0: x -> x + 1`. In `torsion2_scan.py` notation, `E = [(1,0),(-1,0),(-1,1),(1,1)]`
and `F = [(-1,1),(1,-1),(1,0),(1,1)]`.

Two remarks on the table:
- The `Z/7` configuration with `F = E^-1` has the same value `5/6` as the `Z/3` fake.
- Both `(Z/2)^2` fakes and the `Z/7` fakes have `<F F^-1>` finite, so `lambda(F) = 1`. `D_inf` is amenable. By `bernoulli-window-codeword-folner-ratio-bound`, domination is true in every case, and only the method fails.

**Consequence** (claim `shannon-window-fakes-on-klein-and-infinite-dihedral-hosts`, OPEN pending re-referee). The
minimal-window method fails in every group containing:
- an element of order divisible by 3, 4, 5 or 7; or
- two distinct involutions whose product has even or infinite order.

For even `n >= 4`, the dihedral group contains the central involution `(ss')^(n/2)`, and with it `(Z/2)^2`. If all torsion has 2-power order, the method
survives only in torsion-free groups and in groups with exactly one involution.

## 4. Scans

| host | configurations | how chosen | LP < 1 | min LP | file |
|---|---|---|---|---|---|
| `(Z/2)^2` | 40 | random | 15 | 7/9 | `rs_k2.txt` |
| `D_inf` | 80 | random, ball radius 3 | 3 | 7/8 | `rs_dinf.txt` |
| `Z × Z/2` | 80 | random, ball radius 3, `n <= 13` | 0 | 1 | `rs_zz2.txt` |
| `Z × Z/2` | 338 | exhaustive: `E ∋ 1` in the box `[-1,1] × Z/2`, `|E| ∈ {3,4}`, at least 2 readers from `E^-1`, at most 1 non-reader, `n <= 11` | 0 | 1 | `ex_zz2.txt` |
| `Z/7` | 10 | shape `|E| = 4`, `F = ±E + c`, up to automorphisms and re-centring | 5 | 5/6 | `cps_z7.txt` |
| `Z/11` | 21 of 56 classes | same shape, `n <= 14`; stopped by hand after the `E = {0,1,2,3}` and part of the `E = {0,1,2,4}` classes, since single LPs took up to 630 s | 0 | 1 | `cps_z11.txt` |
| Hantzsche–Wendt `P` | 150 | random, at least 2 readers, `n <= 12` | 0 | 1 | `rs_hw_seed7.txt` |
| `Z`, dense | 2 | `E = {0..m-1}`, `F = {0,...,-(m-1)}`, `m = 4, 5` (`n = 11, 14`) | 0 | 1 | `dense_z_large.txt` |

`P` is realised as affine maps of `Z^3` by `a = (X+1, -Y+1, -Z)` and `b = (-X, Y+1, -Z+1)`. `hw_scan.py selftest` checks torsion-freeness on a ball and the defining relations.
`P` is torsion-free, not left-orderable and has no unique products (Promislow). So it is the natural torsion-free host in which a
left-order or unique-product proof of certification cannot apply. Every one of its 150 configurations certifies.

**Z x Z/2.** No fake appears in 418 configurations. The central involution alone seems not to support a minimal-window fake.
This is evidence only, and the question stays open.

**Z/11.** The `Z/7` shape gives no fake in the part of the scan recorded in the file. For `p >= 11`, a 4-element `E` has
`|E + F| <= 16`, and a fake has to wrap the window around `Z/p`. The ground set then grows with `p`, and the LP cost with it.

## 5. Unique products do not govern the fakes (`up_census.py`, output `up_census.txt`)

Call `(F, E)` a UP pair if some product in `FE` has a unique representation. Tabulated over the earlier census outputs:
- `Z/5`: 3 exhaustive and 2 random fakes are UP pairs, among them `E = {0,1,2}`, `F = {0,2,4}` at LP `0.916667`.
- `Z/7`: 2 of 6 fakes are UP pairs, including the `1264/1469` configuration.
- `Z × Z/3`: all 6 fakes are UP pairs.

So unique products within the window neither prevent fakes nor predict them. The obstruction is the presence of a finite
orbit, or a pair of involutions, in the window's translation structure. The unique-product property of the pair is not what matters.

## 6. Commensurability

`D_inf ⊇ Z` with index 2. The `Z` census certifies every tested window (27 exhaustive, 9 dense, up to `n = 14`), while
`D_inf` carries a `7/8` fake. This is evidence, not proof, that `Z` certifies: full certification over `Z` is part of the open
`torsion-free-windows-have-minimal-shannon-certificates`. (Non-invariance under finite-index overgroups does hold by an easy example:
the trivial group certifies, `Phi = h(x_1 y_1) >= h(x_1) = 1`, and it has index 3 in `Z/3`, which has a `5/6` fake.) A proof of
`torsion-free-windows-have-minimal-shannon-certificates` cannot run through virtual torsion-freeness alone, since `D_inf` is virtually `Z`. It has to use torsion-freeness of
the ambient group directly: every translation cycle among window points has to be an infinite orbit.

Blocking the `D_inf` configuration into `Z` does not transfer the fake. The block configuration on `Z` has
a larger window, and its LP is a different program.

## 7. Limits

- Shannon inequalities only. It is not checked whether any fake is almost entropic.
- Scan values other than those in Section 3 are floating-point HiGHS optima.
- The `Z × Z/2` and `Z/p` (`p >= 11`) cases remain open. They are the only torsion hosts where the method is not known to fail.
