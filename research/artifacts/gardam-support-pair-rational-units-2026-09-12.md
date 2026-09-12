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
| `gardam-support-pair-kernel-formula.py` | checks `kappa_i = #(S cap g_i T g_i) - 1` at the 17 trivial units | `c07d4ca8bc4bdae691eb869429d4532f` |
| `gardam-support-pair-z3-subsets.py` | characteristic-free sub-support check | `9bd1081d08c5c2e1c143a163b8c73d71` |
| `gardam-support-pair-gb-easy.py` | exact Groebner basis over `Q` of the localized system | `a519c334f919c69da12c839936674d9f` |

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
  The Jacobian is rank-deficient over `Q` there as well. At `(g_i, h_j)` with
  `g_i h_j = 1` the linearized system reads `du h_j + g_i dv = 0` with
  `sum du = 0`. So its kernel is exactly `dv = -h_j du h_j` with `supp(du)`
  in `S cap g_i T g_i`, and `kappa_i = #(S cap g_i T g_i) - 1` in every
  characteristic. `gardam-support-pair-kernel-formula.py` confirms the values
  0, 8 and 12 at all 17 trivial units. Solution counts modulo `2^k` grow, as
  Bartholdi's approximate units predict.

## 5. Characteristic-free sub-supports

Let `u` be a unit over any field with `S' = supp(u)` in `S` and
`T' = supp(u^(-1))` in `T`. Then the identity lies in `S'T'`, and no other
product has exactly one representation `g_i h_j`, because that coefficient of
`u u^(-1)` would be one nonzero product. `gardam-support-pair-z3-subsets.py`
encodes this with Boolean indicators and `|S'| >= 2`:

```text
proper (g_1 or g_2 missing): {'result': 'unsat'}
sanity, no restriction: {'result': 'sat', "S'": [0, ..., 20], "T'": [0, ..., 20]}
```

So every nontrivial unit on `(S,T)`, over any field, has `u_1, u_2 != 0`.
This is Gardam's case `(1,2)`.

## 6. Exact Groebner basis over Q

`gardam-support-pair-gb-easy.py` builds the localized system from the product
table: `uv = 1`, `u_1 = 1` and `u_2 w = 1` in
`Q[u_1..u_21, v_1..v_21, w]`, 123 equations in all. It runs under Sage 10.7
(MSI module `sagemath/10.7`) as Slurm job 561405.

An earlier version of the script (md5 `11feb3a005a35fe748c9c5cb36993d92`)
confirmed that the generated system equals the zenodo `easy.ms`. It then
stalled, because Sage's ideal methods recomputed the basis with the default
`std`. The current version reads everything off the one computed basis.

```text
equations: 123  [0.0s]
GB over QQ (libsingular:slimgb): 83 elements  [2.0s]
Buchberger criterion over QQ (is_groebner): True
every input equation reduces to 0 mod G: True
max |coefficient| in G: 1
equals zenodo groebner_basis.txt (as sets): True
wrote gb_easy2_qq.json  [3.0s]
dimension: 0  [3.0s]
vector_space_dimension: 16  [3.0s]
elimination ideal in u7, u10: [u10^4 + 1, u7^4 + 1]  [3.0s]
rational points: []  [4.1s]
real algebraic points: 0  [4.6s]
DONE
```

## 7. Conclusion

Let `K` be a field of characteristic zero and `u` a nontrivial unit on
`(S,T)` over `K`. By Section 5, `u_1, u_2 != 0`. Rescaling gives a `K`-point
of the localized ideal `I`. Every point of `I` has `u_7^4 = -1`, so `K`
contains a primitive eighth root of unity. So `Q[P]`, `R[P]`, `Q_2[P]` and
`Z[P]` have no nontrivial unit on `(S,T)`.

Over `Qbar`, `V(I)` maps onto the 16 points of `V(u_7^4+1, u_10^4+1)`, and
`dim_Q Q[x]/I = 16`. So `V(I)` is exactly 16 reduced points, Gardam's family,
and his "bad prime" caveat is removed.

This agrees with Section 4. The nontrivial residue does not lift mod 4, and
the eight nonsingular trivial residues contain only trivial units.

*Trust surface.* Singular `slimgb` over `Q` is exact. Buchberger's criterion
and the reduction of the generators were checked in the same run. The
inclusion `<G> in I` rests on Singular. The z3 `unsat` verdict of Section 5
has no proof certificate.

Recorded in Cairn as `gardam-support-pair-has-no-rational-units`.
