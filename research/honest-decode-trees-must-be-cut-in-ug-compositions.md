---
rg: 2
id: honest-decode-trees-must-be-cut-in-ug-compositions
kind: claim
title: In any reduction to unique games whose completeness witness decodes outer labels through connected decode trees, if the witness keeps a p-fraction of outer constraints on clean trees with c decode components per site and p/K^(c1+c2) exceeds the outer soundness, the source is in P; so every composition proof of UGC needs decode-tree load kappa with kappa eta' >= p0 - K^c s
distinct_from:
  near-perfect-selectors-die-on-every-rigid-doubled-lec: that is Theorem S* for orientation lifts of composed 2-to-1 games and needs a linear read-out (F1), comparable marginals (F2) and 99% rigidity; this needs no read-out, no marginals and no rigidity, only a poly-time decoder on connected decode sets, and it applies to every reduction into unique games, not only lifts.
  near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp: that is the DKKMS-specific Theorem S; this is instance-free and replaces the star-propagation step of its proof by propagation along an arbitrary clean tree with load accounting.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that uses perfect completeness to propagate exactly; this allows eta' > 0 and pays for it through the load kappa.
  akkstv-rounding-holds-on-all-loop-free-constraint-graphs: that gate uses the spectral gap of the host; this gate uses the decode-tree load and is vacuous or binding independently of the spectrum.
  high-advantage-selector-witnesses-decode-good-outer-labellings: that decodes selector witnesses assumed near a locally honest patchwork on DKKMS; this is the general list-decoding principle behind it, for any unique game and any decoder.
artifacts:
  - experiments/ugc-propagation-load-2026-09-17/check_propagation_load.py
  - experiments/ugc-propagation-load-2026-09-17/check_propagation_load.out
---

**ESTABLISHED.** Route: `honest-decode-trees-must-be-cut-proof`. The proof is
self-contained (an elementary list-decoding argument); it imports nothing.

## Setting (a decoded unique-games reduction)

A promise problem `L` and a deterministic polynomial-time map
`x -> (Phi_x, U_x, {D_z, T_z, Dec_z})` with:

* `Phi_x`: a two-prover game on sites `Z_1 ⊔ Z_2` with label sets of any size,
  an explicit constraint distribution `mu` of polynomial support, each
  constraint `c = (z_1(c), z_2(c), P_c)` with a polynomial-time predicate.
* `U_x`: a unique game with alphabet `[K]` (`K <= poly`), permutation
  constraints and edge weights `w(e)` summing to `1`.
* For each site `z`: a decode set `D_z ⊆ V(U_x)`, a set `T_z` of `U_x`-edges whose
  graph on `V(T_z) ⊇ D_z` has `c_z` connected components each meeting `D_z`,
  and a polynomial-time decoder `Dec_z` mapping any `[K]`-labelling of `D_z`
  to a label of `z`.

We assume `K^(c_z) <= poly(|x|)` (for example `c_z = O(1)`).
For a labelling `sigma` of `U_x`, a site is **clean** if `sigma` satisfies every
edge of `T_z`. Write `c_i = max_(z in Z_i) c_z`.

## Statement

**Theorem P (propagation).** Suppose, for some polynomial-time computable
`p(x), s(x)` with `p > K^(c_1 + c_2) s`:

* (NO) `x notin L` implies `val(Phi_x) <= s`;
* (YES) `x in L` implies there is a labelling `sigma` of `U_x` with
  `Pr_(c ~ mu)[ z_1(c), z_2(c) clean and P_c(Dec(sigma|D_(z_1)), Dec(sigma|D_(z_2))) ] >= p`.

Then `L in P`.

**Corollary L (load law).** Let `kappa_i = max_e Pr_(c~mu)[e in T_(z_i(c))] / w(e)`.
If `sigma` violates edge weight `eta'`, then `Pr_c[z_i(c) dirty] <= kappa_i eta'`.
Hence, if the decoded labels of `sigma` satisfy a `p_0`-fraction of `mu`, then
(YES) holds with `p = p_0 - (kappa_1 + kappa_2) eta'`.

**Corollary U (every composition proof of UGC must cut its honest decode trees).**
Let `L` be NP-hard and let a decoded reduction as above have YES witnesses of
UG value `>= 1 - eta'` whose decoding satisfies a `p_0`-fraction of `mu`. Unless
`P = NP`,

```text
(kappa_1 + kappa_2) * eta'  >=  p_0 - K^(c_1 + c_2) * s .
```

With `p_0 >= 3/4` and `K^(c_1+c_2) s <= 1/4` this reads
`kappa_1 + kappa_2 >= 1/(2 eta')`. The honest violations, of total weight `eta'`,
must dirty a constant fraction of decode trees.

## What it kills (impact type 3)

**Class.** Every NP-hardness proof of Gap-UG (UGC) with the shape
"outer game `Phi` of soundness `s`, UG built over it, completeness witness from
which the outer labels are decoded", at decode-tree load
`kappa < (p_0 - K^c s)/eta'`. This covers composition with local inner tests, all
orientation lifts with a decodable witness (the selector routes), and any
"rigid-core" reduction whose honest encoding is read off a UG-connected block.

**Invariant.** `kappa * eta'` against `p_0 - K^(c_1+c_2) s`.

**Step where every member dies.** Seed propagation: `K` guesses at one vertex of
each component of a clean decode tree reconstruct the witness on `D_z`, so the
outer game becomes list-decodable with lists of size `K^(c_z)`, and the NO
soundness `s < p/K^(c_1+c_2)` is contradicted in polynomial time.

**Survivors (each can fail separately).**

* (V1) **High load.** `kappa >= (p_0 - K^c s)/eta'`: decode trees so long or so
  concentrated that honest noise cuts most of them. KKMO-type long-code
  compositions live here (a long-code block of size `q^R` has load of order its
  size).
* (V2) **Many components.** `c_z` so large that `K^(c_1+c_2) s >= p_0`: the decode
  set is spread over many UG-components of `T_z`, so the outer soundness must be
  below `K^(-c)`.
* (V3) **No decodable witness.** Near-perfect YES labellings from which no
  polynomial-time decoder with bounded load recovers a good outer labelling.
  This is (F4) of `near-perfect-selectors-die-on-every-rigid-doubled-lec`, now
  without (F1) and (F2).
* (V4) **Soundness not tied to an outer game.** Reductions whose NO analysis is
  not a bound `val(Phi_x) <= s` on the decoded game.

For the selector holes: (F1) linear read-out and (F2) marginal comparability of
Theorem S\* are not needed by any member of the class. The survivors of the
near-1 selector route reduce to (V1)-(V3), i.e. to (F3) (`s` not below
`K^(-c)`) and (F4').

**Sanity (artifact).** On 200 random planted instances (`K = 5`, `eta'` in
`{0.01, 0.03, 0.1, 0.3}`), list membership, the load bound and
`E[val] >= p/K^2` hold in every trial; the worst observed
`Pr[dirty]/(kappa eta')` is `0.692`. Always `kappa_i >= E_c|T_(z_i(c))|`
(sum the load inequality over `e`). So at `eta' = 1/2` (the 2-to-2 theorem) the
law is vacuous as soon as decode trees have two edges, as it must be.

This neither proves nor refutes UGC.

## Attempts

* **Proof (2026-09-19, swarm-0917-w14-w14-ugc-last1).** Seed propagation plus
  conditional expectations; see the route.
