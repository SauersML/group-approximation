---
rg: 2
id: robust-uniqueness-bounds-robust-kernel-rank
kind: claim
title: If every near-optimal assignment of a 3LIN instance is rho-close to one coset x* + C with dim C <= r0 (robust uniqueness), then every delta_K-approximate kernel map of rank > r0 fails to be onto X_V on all but a 12 k rho mass of smoothed tuples, so robustly unique YES inputs lie in P^delta_(r0); conversely a generic approximate kernel of rank n yields 2^n pairwise far near-solutions, and robust testability of the homogeneous system implies robust uniqueness
distinct_from:
  exact-kernel-rank-does-not-exclude-flip-violators: that refutes (SF_P) and defines the robust classes P^delta_r only by the kernel maps they exclude; this gives a source-side sufficient condition for membership in P^delta_r that mentions no kernel map, and reduces (P1^rob) to a hardness statement about near-solutions of the 3LIN source.
  good-dkkms-orientations-admit-short-star-lists-on-hard-inputs: that is (SF_P) with exact kernel rank, now refuted; this does not state any star-list property and concerns only which inputs carry approximate kernels.
  star-list-structure-is-circular-on-decodable-yes-inputs: that proves Theorem O given a kernel map with small beta_bad; this shows that on robustly unique inputs no kernel map of rank above r0 has beta_bad below 1 - 12 k rho, so Theorem O and Theorem O' have no input there.
  selector-witness-hypotheses-collapse-to-selector-free-form: that reduces the constant-bias kill to (SF_P) on any NP-hard sub-promise P; this supplies a concrete candidate P, defined without reference to orientations, on which the known violator mechanism is provably absent.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that is the selector hole H1; this is a lemma about the 3LIN source that feeds the constant-bias kill route and leaves H1 open.
artifacts:
  - experiments/ugc-robust-uniqueness-2026-09-17/check_robust_uniqueness_kernel.py
---

**ESTABLISHED.** Route: `robust-uniqueness-bounds-robust-kernel-rank-proof`.

## Setting

The notation is that of `star-list-structure-is-circular-on-decodable-yes-inputs`
(Theorem O, with `beta_bad`), of `dkkms-list-seed-needs-lists-exponential-in-l`
(tuples `U`, smoothed tuples `V`, the spaces `X_U`, `X_V`) and of
`exact-kernel-rank-does-not-exclude-flip-violators` (approximate kernel maps,
Theorem O', the classes `P^delta_r`, (P1^rob), (P2^rob)).

Fix a 3LIN instance with variable set `X` and the `U`-marginal of `G_multi`.
A tuple `U` has `k` equation slots and `3k` variable slots.

* **Equation measure.** `omega(e) := (1/k) E_U [# slots of U equal to e]`.
  Write `val_omega(a)` for the `omega`-mass of equations `a` satisfies and
  `viol_omega(a) := 1 - val_omega(a)`.
* **Variable measure.** `nu(T) := (1/(3k)) E_U [# variable slots of U in T]`
  for `T ⊆ X`. Write `dist_nu(a, b) := nu({v : a_v != b_v})`, and
  `dist_nu(a, S) := min over s in S`.
* For a linear `Phi : F_2^X -> F_2^n` and `z in F_2^n`, put
  `y_z(v) := <z, Phi(e_v)>`. This is an assignment, and `z -> y_z` is linear.
* `X_V` is spanned by the coordinate vectors `e_v`, `v in vars(V)` (a kept
  equation contributes its 3 coordinates, a dropped one a single coordinate),
  and `vars(V) ⊆ vars(U)`. So `Phi` is onto `X_V` iff the vectors `Phi(e_v)`,
  `v in vars(V)`, span `F_2^n`. Write `beta_sur` for the `G_multi` mass on
  which `Phi` is onto `X_V`, so `beta_bad = 1 - beta_sur`.

**Robust uniqueness (RU_(kappa, rho, r0)).** There are an assignment `x*` and a
subspace `C ⊆ F_2^X` with `dim C <= r0` such that every assignment `a` with
`val_omega(a) >= 1 - kappa` has `dist_nu(a, x* + C) <= rho`.

## Statements

**Lemma RU.** Let `x` be an assignment with `val_omega(x) >= 1 - eps_x`, let
(RU_(kappa, rho, r0)) hold with `kappa >= eps_x + delta_K`, and let `Phi` be a
`delta_K`-approximate kernel map of rank `n > r0`. Then some `w != 0` has
`nu(supp y_w) <= 4 rho`, and

```text
beta_sur  <=  12 k rho,      i.e.      beta_bad  >=  1 - 12 k rho .
```

**Corollary M (membership).** Call `Phi` generic when `beta_bad <= beta0`.
Here `beta0 < 1` is whatever genericity threshold defines `P^delta_r`. For
item 1 of Theorem O' to give value `> 1/2 + gamma` one needs
`beta0 < v(l) - 1/2 - gamma - 2^(l-k) - delta_dirty - delta`, so
`beta0 < 0.11` at `l >= 8`. The corollary holds for every threshold.

Let the YES input have completeness `1 - eps`, put `delta := gamma'/(4k)`, and
suppose (RU_(eps + delta, rho, r)) holds with `12 k rho < 1 - beta0`. Then
the input lies in `P^delta_r`. Hence

> **(P1^RU)** "(RU-YES, NO) is NP-hard", where RU-YES is the set of YES inputs
> satisfying (RU_(eps + gamma'/(4k), rho, r)) with `rho < (1 - beta0)/(12k)`,

implies (P1^rob) for the same `r`, since RU-YES ⊆ `P^delta_r` and NO is unchanged.

**Proposition C (converse: robust kernels are separated near-solution
families).** Let `Phi` be a `delta_K`-approximate kernel map of rank `n` with
`beta_bad <= beta`, and let `val_omega(x) >= 1 - eps_x`. Then the `2^n`
assignments `x + y_z` all have `val_omega >= 1 - eps_x - delta_K`, and for
`z != z'`,

```text
dist_nu(x + y_z, x + y_(z'))  >=  (1 - beta) / (3k) .
```

So (RU_(eps_x + delta_K, rho, r0)) fails for every `r0 < n` once
`rho < (1 - beta)/(12k)`. This is the contrapositive of Lemma RU. The distance
bound says more: what robust uniqueness excludes is exactly a large affine
family of pairwise far near-solutions.

**Proposition T (robust testability implies robust uniqueness).** Let `C` be the
exact homogeneous kernel and suppose the homogeneous system is `eps0`-robustly
testable: `viol^hom_omega(y) >= eps0 * dist_nu(y, C)` for every `y`. If
`val_omega(x) >= 1 - eps_x`, then (RU_(kappa, (kappa + eps_x)/eps0, dim C))
holds with `x* = x`. With `kappa = eps + gamma'/(4k)` and `eps_x = eps`,
Corollary M applies as soon as

```text
eps0  >  (3 gamma' + 24 k eps) / (1 - beta0) .
```

Since `viol^hom_omega(y) <= 3 dist_nu(y, C)` always holds (each variable
carries a third of the slot mass of its equations), this asks for a constant
fraction of the largest possible testing ratio, not for anything growing in `k`.

**Remark P (product slots).** If the `U`-marginal is the product of `k` copies
of `omega`, then the dirty equations have `omega`-mass at most
`delta_K / (k (1 - delta_K))`, and Lemma RU holds with
`kappa >= eps_x + delta_K/(k(1 - delta_K))`.

## Sanity checks

* **J-instances.** A J-instance with `N` copies of `F_2^n \ 0` has exact
  kernel rank `N n`, and LS Step 7 gives generic kernel maps of rank `n`. It
  satisfies RU with `C` the full linear kernel (`r0 = N n >= n`), which is
  consistent with Lemma RU. By Proposition C it fails RU for every `r0 < n` at
  `rho < (1 - beta)/(12k)`.
* **J'-instances.** These have exact kernel `0`, but `Phi(v) = v` is a
  `delta_K`-approximate generic kernel map. By Proposition C they fail RU for
  every `r0 < n`, so they are not in RU-YES at small `r0`. The violator of
  Corollary R in the J'-node therefore does not refute (P2) on RU-YES.
* **Brute force.** The artifact checks the finite core (items (a), (b) of the
  route's Step 2 and Step 3) on 12 random planted 3LIN instances
  (`N = 9..11`, `m = 2N` or `3N`, noise `0` or `0.05`) and on the J-copy of
  `F_2^4 \ 0`. For every removal set of at most 2 equations (1 for the J-copy), it checks that
  every `y` in the kernel of the remaining equations is within `2 rho` of `C`,
  and that some nonzero `y` has weight `<= 4 rho` whenever that kernel is larger
  than `C`. There are 4124 checks, 7 of which trigger the pigeonhole case, and
  all pass.

## What this changes (impact type 2)

(P1^rob) was stated through the kernel maps it excludes, and so through the
DKKMS tuple structure. Corollary M replaces it by a statement about the 3LIN
source alone: hardness of Gap3Lin on instances whose near-optimal solutions
are unique up to a small linear space and a `rho < (1-beta0)/(12k)` error.
Each of the following can fail independently:
* **(P1^RU)**, NP-hardness of Gap3Lin with robustly unique YES solutions, is
  `gap3lin-hard-with-robustly-unique-yes-solutions`;
* **(P2^RU)**, the selector-free star-list statement (P2) restricted to
  RU-YES, is `dkkms-orientations-admit-star-lists-on-robustly-unique-inputs`.

On RU-YES with `r0 < l + 2` there is no generic approximate kernel map of the
rank Theorem O needs, so the only known violator mechanism (the flip
orientation of Theorems O and O') has nothing to act on. Proposition C shows
that robust uniqueness excludes exactly what the flip needs: a `2^n` affine
family of far-apart near-solutions.

## Attempts

* **2026-09-20, swarm-0917-w20-w20-ugc-pull (finite-models / transplanter).**
  Proved Lemma RU, Corollary M and Propositions C and T, and checked the
  finite core by brute force. Not done: any hardness result for RU-YES, and
  the extension of Corollary D to randomized one-sided reductions (which would
  let Valiant–Vazirani-style isolation be used for (P1^RU)).
