# Gardam's 21-element support pair over Z, Q and Q_2

Lane `unit-conjecture-integral`, 2026-09-12. All computation ran on MSI.

## 1. Setup

`S` and `T` are the ordered 21-element subsets of the Promislow group `P`
given in Gardam's `unit_problem.py` (zenodo 14008425, accompanying
arXiv:2312.05240). They are the supports of `alpha` and `beta` in the proof of
Theorem A. Group elements are 4x4 integer affine matrices, with `a` and `b` as
in the paper. The unknowns are `u in K^S` and `v in K^T`. The equations are
the 121 coefficients of `uv = 1`, and, where stated, the augmentation
normalization `sum u = sum v = 1`.

| script | role | md5 of the run copy |
|---|---|---|
| `gardam-support-pair-gsp.py` | builds `S`, `T`, rechecks Theorem A exactly, writes the product table | `1debc5ec75d10b1b92b6e688a385f916` |
| `gardam-support-pair-f2enum.c` | enumerates every `F_2`-point of `uv = 1` on `(S,T)` | `d2b921a576eeef77e333a03793f0a571` |
| `gardam-support-pair-lift.py` | Jacobian ranks and 2-adic lifting at every `F_2`-point | `89871eb0a295e1319cc60440409bcfad` |

## 2. Theorem A, rechecked exactly

Arithmetic runs in `R[P]` with `R = Z[s,t]/<s^4+1, t^4+1>`, using exact
integer coefficients.

```text
part1 |supp alpha| = 21 |supp beta| = 21
part1 alpha*beta == 1: True  beta*alpha == 1: True
part1 supp(alpha) == S: True  supp(beta) == T: True
part1 coefficients are signed monomials: True
part2 products K = 121 identity index 0 reps at identity 17 odd-count products [0]
part2 trivial pairs (g_i h_j = 1): 17
```

## 3. Every F_2-point

`f2enum` walks all `2^21` vectors `u` in Gray-code order and solves the linear
system `A(u) v = e_1` over `F_2` exactly. It ran in 14.7 s.

```text
u with solvable system: 18, total F_2 points: 18
```

These are the 17 trivial units `u = g_i`, `v = g_i^(-1)`, and the single
full-support point `u = sum S`, `v = sum T`, which is Gardam's `F_2` unit. No
`F_2` unit has a proper nontrivial sub-support of `(S,T)`.

## 4. 2-adic lifting

Normalize a unit of `Z_2[P]` by its augmentation sign. Its residue mod 2 is
one of the 18 points. Put `F` = the 121 bilinear equations plus the two
normalizations, and `J` = the Jacobian of `F`. Because `F` is quadratic and
`2k >= k+1`, the lifts of a solution `x mod 2^k` to `2^(k+1)` are exactly the
`x + 2^k d` with `F(x)/2^k + J(xbar) d = 0` over `F_2`. So each class has
either 0 or `2^kappa` lifts, where `kappa = dim ker J(xbar) mod 2`.

| residue (u index, v index) | rank of `J mod 2` | `kappa` | rank over `Q` (lower bound) | solution counts mod `2, 4, 8, ...` |
|---|---|---|---|---|
| full support (Gardam's `F_2` unit) | 40 | 2 | 40 | 1, **0** |
| (13,16) (14,15) (15,14) (16,13) (17,20) (18,19) (19,18) (20,17) | 42 | 0 | 42 | 1, 1, 1, 1, 1, 1, 1 |
| (0,0) | 34 | 8 | 34 | 1, 256, 256, 65536, 65536, > 2^20 |
| (5,5) (6,6) (11,12) (12,11) | 34 | 8 | 34 | 1, 256, 1024, 65536, 262144, > 2^20 |
| (1,1) (2,2) (3,4) (4,3) | 30 | 12 | 30 | 1, 4096, 4096, > 2^20 |

Indices are 0-based positions in `S` and `T`.

**Consequences.**

* *Case B is closed on `(S,T)`.* No unit of `Z_2[P]` supported on `(S,T)`
  reduces mod 2 to Gardam's `F_2` unit, because the residue has no solution
  mod 4.
* *Case A at the eight nonsingular trivial residues.* If `J(xbar)` is
  injective mod 2 and `x` is a 2-adic solution with `x = xbar mod 2`, write
  `x = xbar + 2^m d` with `d` not zero mod 2. Then `0 = F(x) - F(xbar) =
  2^m J(xbar) d + 2^(2m) Q(d)`, so `J(xbar) d = 0 mod 2` and `d = 0 mod 2`, a
  contradiction. So each of these eight classes contains only the trivial
  unit.
* *Case A at the nine singular trivial residues is not decided by lifting.*
  The Jacobian is rank-deficient over `Q` there as well. The first-order
  deformations `g_i + eps du`, `g_i^(-1) - eps g_i^(-1) du g_i^(-1)` with
  `supp(du)` in `S cap g_i T g_i` and `sum du = 0` all satisfy the
  linearized system. Solution counts modulo `2^k` grow, as Bartholdi's
  approximate units predict.
