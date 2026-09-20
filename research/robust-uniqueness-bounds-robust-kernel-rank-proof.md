---
rg: 2
id: robust-uniqueness-bounds-robust-kernel-rank-proof
kind: route
title: The coordinate functionals y_z of an approximate kernel map are near-kernel assignments, so x + y_z lies in the robust-uniqueness basin and each y_z is 2 rho-close to C; pigeonhole over 2^n > |C| gives a nonzero y_w of nu-weight <= 4 rho, and Phi misses w-perp on every smoothed tuple whose variables avoid supp y_w, a set of mass >= 1 - 12 k rho
target: robust-uniqueness-bounds-robust-kernel-rank
requires:
  - star-list-structure-is-circular-on-decodable-yes-inputs
  - dkkms-list-seed-needs-lists-exponential-in-l
  - exact-kernel-rank-does-not-exclude-flip-violators
artifacts:
  - experiments/ugc-robust-uniqueness-2026-09-17/check_robust_uniqueness_kernel.py
---

The notation is that of the target. The required nodes supply only definitions:
* `beta_bad` and genericity come from Theorem O;
* the description of `X_V` comes from LS (smoothing keeps a 3-coordinate block
  per kept equation and one coordinate per dropped equation);
* approximate kernel maps and `P^delta_r` come from the J'-node.

No step uses a complexity assumption.

## Step 1: y_z is a near-kernel assignment

Let `D` be the set of equations `e` with `Phi(x_e) != 0` (dirty equations). For
every `z`, the assignment `y_z` satisfies the homogeneous equation `e`
(`y_z(u) + y_z(v) + y_z(w) = <z, Phi(x_e)> = 0`) unless `e ∈ D`. A tuple has
at most `k` equation slots, so

```text
omega(D) = (1/k) E_U [# slots of U in D]  <=  (1/k) * k * Pr_U[U meets D]  <=  delta_K .
```

So `x + y_z` violates only equations violated by `x` or lying in `D`, and
`val_omega(x + y_z) >= 1 - eps_x - delta_K >= 1 - kappa`. (Remark P: if slots
are i.i.d. with law `omega`, then `delta_K >= 1 - (1 - omega(D))^k >= k omega(D) (1 - delta_K)`,
because `(1-p)^(k-1) >= (1-p)^k >= 1 - delta_K`. This gives the sharper bound
on `omega(D)`.)

## Step 2: every y_z is 2 rho-close to C

Take `z = 0` in Step 1. Then `x` itself is in the basin, so
`x = x* + c_0 + f_0` with `c_0 ∈ C` and `nu(supp f_0) <= rho`. For each `z`,
`x + y_z = x* + c_z + f_z` with `c_z ∈ C` and `nu(supp f_z) <= rho`. Subtracting,

```text
y_z  =  c'_z + g_z,     c'_z := c_z + c_0 ∈ C,     g_z := f_z + f_0,     nu(supp g_z) <= 2 rho .
```

This is item (a) of the artifact.

## Step 3: pigeonhole

The map `z -> c'_z` goes from `F_2^n` (with `2^n` elements) to `C` (with at most `2^(r0) < 2^n` elements).
So there are `z != z'` with `c'_z = c'_(z')`. Put `w := z + z' != 0`. By
linearity, `y_w = y_z + y_(z') = g_z + g_(z')`, so
`nu(supp y_w) <= 4 rho`. This is item (b) of the artifact.

## Step 4: non-surjectivity off supp y_w

Let `T := supp y_w`. If `vars(V) ∩ T = ∅`, then `<w, Phi(e_v)> = y_w(v) = 0`
for every `v ∈ vars(V)`. Since `X_V` is spanned by these `e_v`,
`Phi(X_V) ⊆ w^perp`, which is a proper subspace because `w != 0`. So `Phi` is not onto `X_V`.

## Step 5: the mass bound

`vars(V) ⊆ vars(U)`, so

```text
beta_sur  <=  Pr_U[ some variable slot of U lies in T ]
          <=  E_U[# variable slots of U in T]  =  3k nu(T)  <=  12 k rho .
```

This proves Lemma RU.

## Corollary M

Let `Phi` be a `delta`-approximate kernel map of rank `> r` on an input with
(RU_(eps + delta, rho, r)). The YES assignment has `eps_x <= eps`, so Lemma RU
applies with `delta_K = delta` and gives `beta_bad >= 1 - 12 k rho > beta0`.
So `Phi` is not generic, and every generic `delta`-approximate kernel map has
rank `<= r`. That is membership in `P^delta_r`.

For (P1^RU) implies (P1^rob): any Karp reduction from an NP-hard problem to
`(RU-YES, NO)` is also a reduction to `(P^delta_r, NO)`, because RU-YES ⊆
`P^delta_r`, the NO side is the same, and the map is unchanged.

## Proposition C

By Step 1, each `x + y_z` has `val_omega >= 1 - eps_x - delta_K`. For
`z != z'`, `(x + y_z) + (x + y_(z')) = y_w` with `w = z + z' != 0`. By Step 4,
on every `V` where `Phi` is onto `X_V`, some `v ∈ vars(V)` has `y_w(v) != 0`.
So `1 - beta <= beta_sur <= Pr_U[U meets supp y_w] <= 3k nu(supp y_w)`, which
gives `dist_nu >= (1 - beta)/(3k)`. The failure of RU is Lemma RU read
contrapositively: RU with `r0 < n` and `rho < (1-beta)/(12k)` would force
`beta_bad >= 1 - 12 k rho > beta`.

## Proposition T

Let `a` have `val_omega(a) >= 1 - kappa`. The homogeneous equations violated by
`a + x` are among those violated by `a` or by `x`, so
`viol^hom_omega(a + x) <= kappa + eps_x`. Testability gives `c ∈ C` with
`dist_nu(a + x, c) <= (kappa + eps_x)/eps0`, that is, `a` is that close to
`x + c ∈ x + C`.

The numeric condition follows by substituting `kappa + eps_x = 2 eps + gamma'/(4k)`
into `12 k rho < 1 - beta0`.

For the upper bound `viol^hom <= 3 dist_nu`: let `c` be nearest to `y` and
`S := supp(y + c)`. Then `y` violates only equations meeting `S`. The slot
identity gives `nu(v) = (1/3) sum over e containing v of omega(e)` (each
equation has 3 variable slots), and so
`omega(equations meeting S) <= sum over v in S of 3 nu(v) = 3 nu(S)`.

## Artifact

`experiments/ugc-robust-uniqueness-2026-09-17/check_robust_uniqueness_kernel.py`
exhausts all assignments on 12 random planted instances and on the J-copy of
`F_2^4 \ 0`. For each instance it:
* sets `C` to the exact homogeneous kernel, and additionally to `{0}` when that
  kernel is nontrivial;
* ranges over every removal set `R` of at most 2 equations (at most 1 for the
  J-copy);
* sets `rho` to the true RU radius at `kappa = eps_x + |R|/m`;
* checks items (a) and (b) for `Y = ker(H|_(E \ R))`, which is the finite form
  of Steps 2 and 3 with `D = R`.

The run gives `ALL PASS`, with exit code 0.
