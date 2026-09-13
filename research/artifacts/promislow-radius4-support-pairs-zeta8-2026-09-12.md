# Units in characteristic 0 on the radius-four census pairs (2026-09-12)

Claim: `research/promislow-radius4-support-pairs-need-zeta8.md`.
Route: `research/promislow-radius4-support-pairs-need-zeta8-proof.md`.

All runs used Sage 10.7 (`sage -python`) on MSI, partition `agsmall`, in a
directory holding the ancillary files of arXiv:2608.00103v1.

| script (name on MSI) | md5 | slurm job |
| --- | --- | --- |
| `promislow-radius4-census.py` (`census.py`) | `a176df8f7ddf4c4f15953a67871d4eb2` | 584612 |
| `promislow-radius4-census-points.py` (`census_points.py`) | `ca739a6bffc4b9aca63677e04e2057d8` | 588135 |
| `promislow-radius4-census-verify.py` (`census_verify.py`) | `93e8f3bfc7197a0b82419fa96905334d` | 590737 |

Inputs from the arXiv ancillary files: `census52.json` (md5
`8f51cffbea19199424772e315aae0a94`) and `box_b4_syllable_intersect.json` (md5
`59f16ea752b7493c7325ebad292f6f77`). `census_pairs.json`, written by mode
`orbits` and read by the other two scripts, has md5
`88d50831522fe612ef9412f27237bfb3`.

Job 584612 ran `census.py orbits`, then `census.py cases k QQ 1800 inv` for
`k = 0..6` in sequence. In parallel it ran the box variants, recorded at the
end.

## Mode `orbits` (job 584612)

Verbatim:

```text
52 units, box 155, |B(4)| = 83  [0.0s]
automorphisms permuting the generators: 8  [0.0s]
orbit 0: size 8, |T| = 21, radius of T 5, cells 121, trivial pairs 17, J mod 2 rank 40/42, depth one infeasible: the residue has no Z_2-lift on this pair  [0.5s]
orbit 1: size 8, |T| = 21, radius of T 5, cells 121, trivial pairs 17, J mod 2 rank 40/42, depth one infeasible: the residue has no Z_2-lift on this pair  [0.6s]
orbit 2: size 8, |T| = 21, radius of T 4, cells 121, trivial pairs 17, J mod 2 rank 40/42, depth one infeasible: the residue has no Z_2-lift on this pair  [0.7s]
orbit 3: size 8, |T| = 21, radius of T 4, cells 121, trivial pairs 17, J mod 2 rank 40/42, depth one infeasible: the residue has no Z_2-lift on this pair  [0.8s]
orbit 4: size 8, |T| = 21, radius of T 4, cells 121, trivial pairs 17, J mod 2 rank 40/42, depth one infeasible: the residue has no Z_2-lift on this pair  [0.9s]
orbit 5: size 8, |T| = 21, radius of T 4, cells 121, trivial pairs 17, J mod 2 rank 40/42, depth one infeasible: the residue has no Z_2-lift on this pair  [1.0s]
orbit 6: size 4, |T| = 21, radius of T 4, cells 121, trivial pairs 17, J mod 2 rank 40/42, depth one infeasible: the residue has no Z_2-lift on this pair  [1.1s]
DONE
```

Orbits 0 and 1 have inverse support of word radius 5. They account for the
16 units whose inverse leaves `B(4)`, as in Tabei's census.

The depth-one column is a cross-check that uses no Groebner basis. Write a
unit of `Z_2[P]` on the pair that reduces to `(u_0, u_0^(-1))` as
`u_0 + 2s` and `u_0^(-1) + 2t`, scaled to augmentation 1. Then `u v = 1`
modulo 4 is a linear system over `F_2` in `(s, t)`, and it has no solution.
This excludes lifts of the residue `u_0` itself, not other units on the
pair.

## Mode `cases` over `Q`, `T` the inverse support (job 584612)

Verbatim:

```text
orbit 0: |S| = 21, |T| = 21 (inv), cells 121  [0.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 0 QQ case (0,1): GB size 82, dim 1, vdim -1  [3.1s]
orbit 0 QQ: nonempty cases [(0, 1)]; timeouts []  [27.0s]
DONE
orbit 1: |S| = 21, |T| = 21 (inv), cells 121  [0.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 1 QQ case (0,1): GB size 82, dim 1, vdim -1  [3.9s]
orbit 1 QQ: nonempty cases [(0, 1)]; timeouts []  [24.9s]
DONE
orbit 2: |S| = 21, |T| = 21 (inv), cells 121  [0.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 2 QQ case (0,1): GB size 120, dim 1, vdim -1  [2.9s]
orbit 2 QQ: nonempty cases [(0, 1)]; timeouts []  [29.5s]
DONE
orbit 3: |S| = 21, |T| = 21 (inv), cells 121  [0.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 3 QQ case (0,1): GB size 120, dim 1, vdim -1  [2.9s]
orbit 3 QQ: nonempty cases [(0, 1)]; timeouts []  [28.2s]
DONE
orbit 4: |S| = 21, |T| = 21 (inv), cells 121  [0.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 4 QQ case (0,1): GB size 120, dim 1, vdim -1  [2.5s]
orbit 4 QQ: nonempty cases [(0, 1)]; timeouts []  [22.4s]
DONE
orbit 5: |S| = 21, |T| = 21 (inv), cells 121  [0.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 5 QQ case (0,1): GB size 120, dim 1, vdim -1  [2.8s]
orbit 5 QQ: nonempty cases [(0, 1)]; timeouts []  [22.6s]
DONE
orbit 6: |S| = 21, |T| = 21 (inv), cells 121  [0.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 6 QQ case (0,1): GB size 147, dim 1, vdim -1  [80.3s]
orbit 6 QQ: nonempty cases [(0, 1)]; timeouts []  [126.1s]
DONE
```

A case is printed only if its basis has no nonzero constant, so the other 209
cases of each representative are empty over `Q`. In case `(0,1)` the variable
`u0` has been replaced by 1 but is still a ring variable, and no equation
involves it. That is the extra dimension: `dim 1` here is dimension 0 in the
other variables, as the next run confirms. The Singular warnings come from
`dim` and `vdim` applied to the `slimgb` output and do not affect the results.

## Case `(0,1)` without `u0` (job 588135)

Verbatim:

```text
// ** _ is no standard basis
orbit 0: |S| = 21, |T| = 21, GB size 82, dim 0  [3.5s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 0: length 16, standard monomials 16  [3.5s]
orbit 0: charpoly degree 16, squarefree True, real roots 0, factor degrees over QQ [4, 4, 4, 4]  [3.6s]
orbit 0: factor degrees over QQ(zeta_8) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]  [3.7s]
// ** _ is no standard basis
orbit 1: |S| = 21, |T| = 21, GB size 82, dim 0  [7.3s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 1: length 16, standard monomials 16  [7.3s]
orbit 1: charpoly degree 16, squarefree True, real roots 0, factor degrees over QQ [4, 4, 4, 4]  [7.3s]
orbit 1: factor degrees over QQ(zeta_8) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]  [7.3s]
// ** _ is no standard basis
orbit 2: |S| = 21, |T| = 21, GB size 120, dim 0  [10.1s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 2: length 16, standard monomials 16  [10.1s]
orbit 2: charpoly degree 16, squarefree True, real roots 0, factor degrees over QQ [4, 4, 4, 4]  [10.1s]
orbit 2: factor degrees over QQ(zeta_8) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]  [10.2s]
// ** _ is no standard basis
orbit 3: |S| = 21, |T| = 21, GB size 120, dim 0  [13.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 3: length 16, standard monomials 16  [13.0s]
orbit 3: charpoly degree 16, squarefree True, real roots 0, factor degrees over QQ [4, 4, 4, 4]  [13.0s]
orbit 3: factor degrees over QQ(zeta_8) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]  [13.0s]
// ** _ is no standard basis
orbit 4: |S| = 21, |T| = 21, GB size 120, dim 0  [16.0s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 4: length 16, standard monomials 16  [16.0s]
orbit 4: charpoly degree 16, squarefree True, real roots 0, factor degrees over QQ [4, 4, 4, 4]  [16.0s]
orbit 4: factor degrees over QQ(zeta_8) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]  [16.0s]
// ** _ is no standard basis
orbit 5: |S| = 21, |T| = 21, GB size 120, dim 0  [18.9s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 5: length 16, standard monomials 16  [18.9s]
orbit 5: charpoly degree 16, squarefree True, real roots 0, factor degrees over QQ [4, 4, 4, 4]  [18.9s]
orbit 5: factor degrees over QQ(zeta_8) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]  [18.9s]
// ** _ is no standard basis
orbit 6: |S| = 21, |T| = 21, GB size 147, dim 0  [147.7s]
// ** _ is no standard basis
// ** _ is no standard basis
orbit 6: length 16, standard monomials 16  [147.7s]
orbit 6: charpoly degree 16, squarefree True, real roots 0, factor degrees over QQ [4, 4, 4, 4]  [147.7s]
orbit 6: factor degrees over QQ(zeta_8) [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]  [147.7s]
DONE
```

The linear forms `L` and the polynomials `cp` are in `census_points_k.txt` on
MSI (`/scratch.global/sauer354/uc0/t00103/anc`).

## Group-law check of the 16 points (job 590737)

`promislow-radius4-census-verify.py` first asserts that the product table,
the number of cells, the identity cell and the trivial pairs recomputed from
the group law equal those in `census_pairs.json`. Then, for each
representative, it recomputes `I_01` and asserts that `cp` is squarefree of
degree equal to the length. It finds the coordinates as polynomials in `L`
from the powers `nf(1) M^i` of the multiplication matrix, and evaluates them
at the roots of `cp` in `Q(zeta_8)`. Output lines, verbatim, with the Singular
warnings removed:

```text
orbit 0: size 8, trivial pairs 17, case (0,1) points 16, distinct 16, u v = 1 for all: True, coordinates generate QQ(zeta_8) (none real): True  [3.9s]
orbit 1: size 8, trivial pairs 17, case (0,1) points 16, distinct 16, u v = 1 for all: True, coordinates generate QQ(zeta_8) (none real): True  [7.6s]
orbit 2: size 8, trivial pairs 17, case (0,1) points 16, distinct 16, u v = 1 for all: True, coordinates generate QQ(zeta_8) (none real): True  [10.6s]
orbit 3: size 8, trivial pairs 17, case (0,1) points 16, distinct 16, u v = 1 for all: True, coordinates generate QQ(zeta_8) (none real): True  [13.6s]
orbit 4: size 8, trivial pairs 17, case (0,1) points 16, distinct 16, u v = 1 for all: True, coordinates generate QQ(zeta_8) (none real): True  [16.6s]
orbit 5: size 8, trivial pairs 17, case (0,1) points 16, distinct 16, u v = 1 for all: True, coordinates generate QQ(zeta_8) (none real): True  [19.5s]
orbit 6: size 4, trivial pairs 17, case (0,1) points 16, distinct 16, u v = 1 for all: True, coordinates generate QQ(zeta_8) (none real): True  [92.6s]
```

`u v = 1 for all` means that each point, multiplied out in `Q(zeta_8)[P]`,
gives 1 at the identity and 0 in every other cell, with `u_1 w = 1`. The last
column means that `zeta_8 -> zeta_8^j` moves some coordinate of every point
for `j = 3, 5, 7`.

An earlier submission of this script (job 589061) computed the powers of `L`
as polynomials, which does not finish in 42 variables. It was cancelled
after 13 minutes with no output and is not part of the evidence.

## Box runs (not evidence)

Job 584612 also ran `census.py cases k 2 1800 box` and
`census.py cases k QQ 3600 box`, with `T` the whole 155-element box, so 600
product cells and 177 unknowns. Verbatim output:

```text
== census_box_2.out
orbit 0: |S| = 21, |T| = 155 (box), cells 600  [0.0s]
orbit 0 2box case (0,1): TIMEOUT 1800s  [1800.1s]
== census_box_QQ.out
orbit 0: |S| = 21, |T| = 155 (box), cells 600  [0.0s]
```

The first case of the first representative did not finish in 30 minutes over
`F_2`, and nothing finished over `Q`. The job was cancelled after the runs
above had finished. So nothing here covers inverse supports other than `T`.
