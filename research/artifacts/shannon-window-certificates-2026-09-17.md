# Shannon window certificates for Rokhlin window domination (2026-09-17)

Agent `a-gs-rokhlin-obstruction`, wave `swarm-0917`, lane obstruction-miner, family census-computation.
Target hole: `every-group-has-positive-rokhlin-entropy-action`, through the normal form
`rokhlin-window-transport-is-dominated` (equivalently Bernoulli maximality, by
`bernoulli-rokhlin-deficit-has-a-finitary-witness`).

Code and raw outputs: `experiments/shannon-window-certificates-2026-09-17/`.

## 1. The question

The graph records these partial proofs of domination `Phi >= log q`:
- sunflowers (Shannon, Proposition 3 of the transport artifact);
- linear codes;
- the codeword Følner count `Phi >= log q / lambda(F)`.

None of them works in general. The open need in
`research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md` says for a neighbouring
problem: "No Shannon-type proof was found, and none has been shown impossible". This census asks the
analogous question for Bernoulli windows, computationally: **which configurations are certified by a
Shannon-type derivation that uses only the random variables of the configuration's own window?**

## 2. The LP

Fix a group `G` and a configuration `(k, E, F, psi)` with `1 in E`. By translation this is WLOG, since
`Phi(E, F) = Phi(gE, F g^-1)`. Normalise `k log q = 1`. The ground set is

    V = { x_g : g in X } u { y_g : g in Y },   X = FE u {1},  Y = F   (the minimal window).

Minimise `Phi = h(y_f0) + h(x_1 u y_F) - h(y_F)` over set functions `h` on subsets of `V` subject to:

- **(P)** all elemental Shannon inequalities, which are equivalent to `h` being a polymatroid;
- **(I)** `h(x_g) = 1` and `h(x_X) = |X|`;
- **(D)** `h(y_g u x_(gE)) = h(x_(gE))` for `g in Y`;
- **(T)** `h(S) = h(tS)` for every `t in G` and every `S` with `S` and `tS` both in `V`.

The entropy vector of a genuine configuration satisfies every constraint. So:

- If the LP value `LP(E,F)` is `>= 1`, LP duality gives a Shannon-type derivation of `Phi >= log q` for that configuration, from these premises.
- If it is `< 1`, no such derivation exists.

Consequences of independence and functional dependence, such as `I(y_A ; x_B | x_(AE ∩ B)) = 0`, follow
from (P), (I) and (D) by data processing, so they are already included. Enlarging `Y` gives a
monotone nondecreasing value `LP_Y`. The codeword Følner count of
`bernoulli-window-codeword-folner-ratio-bound` is exactly a Shannon derivation on the larger ground set
`Y = SF`, `X = SFE ∪ S`.

Implementation (`shannon_lp.py`):
- merge the coordinates identified by (T), using connected components of the translation action on subsets;
- drop duplicate elemental rows;
- solve with HiGHS (interior point for scans, dual simplex for vertex solutions).

Sanity check: the free-group sunflower `E = {1,a,b}`, `F = {1,A,B}` gives LP `1`, matching Proposition 3.

## 3. Census results

"n" is `|V|`. All values are floating-point LP optima unless marked exact.

| host | configurations | how chosen | LP < 1 | min LP |
|---|---|---|---|---|
| `F_2` | 38 | all `|E| = 3` in the unit ball, `|F| = 2` in the 2-ball, up to signed generator permutations (`scan_free_F2.txt`) | 0 | 1 |
| `F_2` | 9 | `|F| = 3`, first 9 of the scan (`scan_free_F3_partial.txt`) | 0 | 1 |
| `F_2` | 3 | random, with at least 2 readers of site 1 (`rs_free.txt`) | 0 | 1 |
| `Z` | 27 | all `E = {0,e1,e2} ⊆ [0,3]`, `|F| ∈ {2,3}` in `[-4,4]`, `n ≤ 12` (`scan_z.txt`) | 0 | 1 |
| `Z` | 7 | dense windows, including `E = {0,...,4}`, `F = {0,1,2,3}` (n = 12) and `E = {0,1,2,4}`, `F = {1,2,3}` (`dense_z.txt`) | 0 | 1 |
| `Z^2` | 17 | random, at least 2 readers (`rs_z2.txt`) | 0 | 1 |
| Heisenberg `H_3(Z)` | 40 | random, at least 2 readers (`rs_heis.txt`) | 0 | 1 |
| `Z/2` | 3 | exhaustive (`cyclic_z2.txt`) | 0 | 1 |
| `Z/3` | 11 | exhaustive up to units (`cyclic_z3.txt`) | 2 | **5/6 exact** |
| `Z/4` | 56 | exhaustive up to units, `n ≤ 12` (`cyclic_z4.txt`) | 12 | **7/9 exact** |
| `Z/5` | 95 | exhaustive up to units, `|E|, |F| ≤ 4`, `n ≤ 10` (`cyclic_z5.txt`) | 26 | 0.785714 |
| `Z/5` | 40 | random (`rs_z5.txt`) | 19 | 0.794872 |
| `Z/7` | 40 | random (`rs_z7.txt`) | 6 | 0.807692 |
| `Z × Z/3` | 40 | random (`rs_zz3.txt`) | 6 | 0.833333 |

**Observation A (torsion-free hosts).** Every one of the 140 distinct torsion-free configurations has
minimal-window LP exactly 1. The hosts were `F_2`, `Z`, `Z^2` and `H_3(Z)`.

**Observation B (torsion).** Every configuration found below 1 has a finite cyclic subgroup `<t>` of order
at least 3, with `E` meeting it in a full or near-full orbit. In each tested case, adding the missing
codewords of that finite orbit to `Y` restores LP 1:
- `Z/3`, `E = {0,1,2}`, `F = {0,1}`: `Y = Z/3` gives LP 1;
- `Z/4`, `E = Z/4`, `F = {0,1,2}`: `Y = Z/4` gives LP 1;
- `Z/5`, `E = {0,1,2,4}`, `F = {1,2,3}`: `Y = Z/5` gives LP 1;
- `Z/5`, `E = {0,1,2}`, `F = {1,2,3,4}`: `Y = Z/5` gives LP 1.

The same windows in `Z` certify: `E = {0,1,2}`, `F = {0,1}` gives 1, and `E = {0,...,4}`, `F = {0,1,2,3}` gives 1,
against 0.746875 in `Z/5`.

**Full-orbit family.** `E = <t> = Z/n`, `F = Z/n minus one element`:

| n | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|
| minimal-window LP | 1 | 5/6 | 7/9 | 0.746875 | 0.726933 |

## 4. Exact fakes

`verify_fake.py n E F` does the following:
1. Takes a vertex solution from the dual simplex.
2. Rationalises it.
3. Rebuilds `h` on all `2^|V|` subsets without variable merging.
4. Checks every elemental inequality, (I), (D) and every translation equality (T) in exact rational arithmetic.
5. Prints `Phi`, then re-solves with `Y = Z/n`.

Output (exit code 0 means exact and `Phi < 1`):

    Z/3 E={0,1,2} F={0,1} ground set size 5; checked 85 elemental inequalities, 32 translation equalities: ALL EXACT
      exact Phi of rationalised polymatroid = 5/6
      LP with Y = Z/3 (closed orbit, ground set 6): 1.000000000
    Z/4 E={0,1,2,3} F={0,1,2} ground set size 7; checked 679 elemental inequalities, 192 translation equalities: ALL EXACT
      exact Phi of rationalised polymatroid = 7/9
      LP with Y = Z/4 (closed orbit, ground set 8): 1.000000000
    Z/5 E={0,1,2,4} F={1,2,3} ground set size 8; checked 1800 elemental inequalities, 384 translation equalities: ALL EXACT
      exact Phi of rationalised polymatroid = 4/5
      LP with Y = Z/5 (closed orbit, ground set 10): 1.000000000

**The `Z/3` fake, in full.** The ground set is `x0, x1, x2, y0, y1`, with `y_g` a function of `(x_g, x_(g+1), x_(g+2))`.
All five variables therefore depend on the same three inputs. The values are:

    h(x_i) = 1, h(y0) = h(y1) = 5/6
    h(x_i x_j) = 2, h(x0 y0) = h(x0 y1) = h(x1 y1) = h(x2 y0) = 5/3, h(x1 y0) = h(x2 y1) = 11/6, h(y0 y1) = 5/3
    h(x0 x1 x2) = 3, h(x0 y0 y1) = 5/3, every other triple = 5/2
    h(x0 x1 x2 y_j) = 3, h(x1 x2 y0 y1) = 3, h(x0 x1 y0 y1) = h(x0 x2 y0 y1) = 5/2
    h(all five) = 3

The 85 elemental inequalities can be checked by hand from this table. The translation `t = +1` maps
`{x0,x1,x2,y0} -> {x1,x2,x0,y1}`, and the 32 translation equalities also hold. So

    Phi = h(y0) + h(x0 y0 y1) - h(y0 y1) = 5/6 + 5/3 - 5/3 = 5/6 .

In the fake:
- `y0` and `y1` are independent, and together they determine `x0`;
- `I(x0 ; y0) = I(x0 ; y1) = 1/6`, and `x1` is independent of `y0` (`h(x1 y0) = 11/6`);
- `I(x0 ; y0 y1) = 1 > 5/6 = h(y0)`.

The genuine inequality needs the third codeword `y2`. With `y2`, the count
`3 = h(x_(Z/3)) <= h(y0 y1 y2) + sum_g h(x_g | y_(g+F)) <= 3 h(y0) + 3 h(x0 | y0 y1)`
gives `Phi >= 1`. This is the Følner count with `S = Z/3`.

## 5. Consequences

1. **Class kill** (claim `minimal-window-shannon-derivations-miss-rokhlin-domination`).
   - Shannon-type derivations restricted to the configuration's own window cannot prove domination.
   - They fail, with exact fakes, in every group with an element of order 3, 4 or 5, and so whenever some element order is divisible by 3, 4 or 5. The Z/7 scan gives floating-point fakes at order 7. Groups whose only torsion has order 2 are not covered: the 3 patterns in `Z/2` all certify.
   - Where they fail, the inequality is true, so this limits proofs and is not a counterexample.
   - The step where every member dies is the final nonnegative combination of elemental inequalities: the polymatroids of Section 4 satisfy every premise and violate the conclusion.
   - All sites and all translations `p q^-1` lie in `<t>`, so the LP is the same in every group containing `t`.
   - Approaches in the class:
     - arguments that manipulate only `x` on `FE ∪ {1}` and `y_F` (per-term transport bounds, sunflower-type conditional independence);
     - any extension of Proposition 3 that adds no codewords.
   - Surviving proofs must add codewords outside `F`, as the Følner count does.
2. **Evidence toward a torsion-free local certificate** (claim
   `torsion-free-windows-have-minimal-shannon-certificates`, OPEN).
   - In the 140 torsion-free configurations, no enlargement was needed.
   - If minimal-window certification holds for every configuration in every torsion-free group, then Bernoulli shifts are Rokhlin-maximal over every torsion-free group, through `bernoulli-rokhlin-deficit-has-a-finitary-witness`.
   - That would include the torsion-free nonsofic groups of `integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic` and `fp-torsion-free-nonsofic-group-of-cd-at-most-three`.
   - It would also give Gottschalk's conjecture for them (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`).
   - The evidence is small-window only, and every tested host is sofic, so the domination inequality itself was already known there. What the census tests is whether the *minimal-window proof method* suffices.
3. **What a Shannon proof of one configuration needs.** For a fixed configuration in `G`, a Shannon-type
   derivation of `Phi >= log q` from (I), (D) and (T) on some finite window exists exactly when `LP_Y(E,F) >= 1`
   for some finite `Y ⊇ F`, with `X = YE ∪ {1}`.
   - Each `LP_Y` is attained, and `LP_Y` is nondecreasing in `Y`.
   - The feasible sets are compact once coordinates are bounded by `|X|`.
   - If `c = sup_Y LP_Y < 1`, a Tychonoff limit of optimal solutions along an exhausting sequence of windows gives a `G`-invariant polymatroid on the finite subsets of `{x_g, y_g : g in G}`. It satisfies (I), (D) and (T) and has `Phi <= c`.
   - Conversely, such an invariant fake with `Phi < 1` restricts to every finite window.
   - So a configuration has a finite Shannon proof iff it has no invariant Shannon fake on all of `G`.
   - The census found no configuration where the fake survives the closing of its finite orbit.

## 6. Limits

- Only Shannon-type inequalities are used. Non-Shannon inequalities (Zhang–Yeung and others) could still certify the torsion fakes on the minimal window. It is not checked whether the fakes of Section 4 are almost entropic.
- The census covers small windows only (`|V| <= 13`) and four torsion-free hosts. Observation A is evidence, not a theorem.
- LP values other than those in Section 4 are floating-point HiGHS optima.
