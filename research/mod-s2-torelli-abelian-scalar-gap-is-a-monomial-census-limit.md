---
rg: 2
id: mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
kind: claim
title: On representations of Mod(S_2) with abelian Torelli image, the operator-norm distance of a separating twist from the cube-root scalars is a monotone limit of explicit lattice distances, equal to 1/15, 1/30, 1/15 at Sp4, Gamma(2), Gamma(3)
distinct_from:
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that asks for a uniform operator-norm gap over all finite-dimensional representations; this computes the gap exactly on the subclass with abelian Torelli image, as an infimum of lattice distances d(Gamma') over finite-index subgroups of Sp4(Z), and evaluates d exactly at levels one to three. It neither proves nor refutes that claim, but the positivity of the limit is a necessary condition for it.
  mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors: its finite-image floor (E4) bounds representations that factor through a finite quotient and is not uniform; this covers representations with infinite image (characters of infinite order of finite-index subgroups, induced up), and its bound is the exact infimum at each level.
  deligne-torelli-character-counts-separating-twists: that excludes an exact cube-root scalar through the single level-one character; this measures the distance through all characters of all finite-index subgroups containing the Torelli group.
artifacts:
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census.py
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/gq24_check.py
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-sp4_theta-odd_theta-even_pt-2_lag-2_plane-2.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-flag-2_pt-3_lag-3_vec-3_plane-3_vecpm-4.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-flag-3_pt-5_lag-5_frame-2.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-pt-7_lag-7_plane-5_line-9_vec-5_frame-3.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-frame-3.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-pt-2+pt-3_theta-even+pt-3_plane-2+lag-3.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-plane-2+plane-3_flag-2+flag-3_pt-3+pt-5_theta-odd+lag-3.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/gq24-check-frame-3.json
---

**ESTABLISHED** through `mod-s2-torelli-abelian-scalar-gap-census-proof`. Unreviewed; no novelty claimed.

**Notation.**
- `M = Mod(S_2)`, `K = I(S_2)` its Torelli group, and `pi : M -> Gamma = Sp_4(Z)` with kernel `K`.
- `t_s = (a_1 a_2)^6` is the separating twist on the Humphries chain, and `omega = exp(2 pi i/3)`.
- `||x||` is the distance from `x` to the nearest integer, for `x` in `R/Z`.
- A finite-dimensional unitary representation `rho` of `M` is **Torelli-abelian** if `rho(K)` is abelian,
  i.e. if `rho` factors through `M/[K,K]`.

**The lattice distance.** Let `Gamma'` have finite index in `Gamma`, and put `M' = pi^(-1)(Gamma')`, so `K <= M'`.
- Pick coset representatives `g_c` for the right cosets `M' g` (index set `X`).
- Let `v_c` be the class of `g_c t_s g_c^(-1)` in `H_1(M'; Z)`. This lies in `M'` because `K` is normal, and
  its class does not change when `g_c` is replaced by `m g_c` with `m in M'`. Set
  ```text
  W(Gamma') = { w in Z^X : sum_c w_c v_c = 0 in H_1(M') }.
  ```
- Define
  ```text
  d(Gamma') = min { max_c || theta_c - 1/3 || : theta in (R/Z)^X , sum_c w_c theta_c = 0 for all w in W(Gamma') } .
  ```
  The feasible set `W^perp` is a closed subgroup of the torus, so the minimum is attained. It does not
  depend on the choice of `g_c`, and `d(Gamma') <= 1/3` (take `theta = 0`).
- Put `d_inf = inf { d(Gamma') : [Gamma : Gamma'] < infinity }`.

**Statement.**

1. **(TA1) Reduction.** For every Torelli-abelian `rho`,
   ```text
   min_(+-) || rho(t_s) - omega^(+-1) I ||_op  >=  2 sin(pi d_inf) .
   ```
   The bound is sharp at every level. For each `Gamma'` there is a character `psi` of `M'` with
   `|| Ind_(M')^M psi (t_s) - omega I ||_op = 2 sin(pi d(Gamma'))`, and `Ind psi` is Torelli-abelian. Hence
   ```text
   inf_(rho Torelli-abelian) min_(+-) || rho(t_s) - omega^(+-1) I ||_op  =  2 sin(pi d_inf) .
   ```
2. **(TA2) Monotonicity and congruence form.** If `Gamma'' <= Gamma'`, then `d(Gamma'') <= d(Gamma')`. Every
   finite-index subgroup contains some `Gamma(N)`. Hence `d_inf = inf_N d(Gamma(N))`, and this is the limit of
   `d(Gamma(N))` along `N` ordered by divisibility.
3. **(TA3) Certificates.** If `w in W(Gamma')` has `3` not dividing `sum_c w_c`, then
   `d(Gamma') >= 1/(3 ||w||_1)`.
4. **(TA4) Census.** In the table, "classes" is the number of distinct `v_c`, which is the number of
   coordinates that matter. The values are exact, because the certificate lower bound of (TA3) equals an
   exact rational feasible point.

   | `Gamma'` | index | `b_1(M')` | classes | `rank W` | cert `||w||_1` | `d(Gamma')` |
   |---|---|---|---|---|---|---|
   | `Sp_4(Z)` | 1 | 0 | 1 | 1 | 5 | 1/15 |
   | odd theta characteristic stabilizer | 6 | 0 | 1 | 1 | 10 | 1/30 |
   | even theta characteristic stabilizer | 10 | 1 | 2 | 1 | 10 | 1/30 |
   | stabilizer of a point of `P^3(F_2)` | 15 | 1 | 2 | 1 | 5 | 1/15 |
   | stabilizer of a point of `P^3(F_3)` | 40 | 1 | 2 | 1 | 5 | 1/15 |
   | stabilizer of a line of `(Z/9)^4` | 1080 | 1 | 2 | 1 | 5 | 1/15 |
   | stabilizer of a nondegenerate plane mod 5 | 650 | 0 | 3 | 3 | 5 | 1/15 |
   | `Gamma(2)` | 720 | 9 | 10 | 1 | 10 | 1/30 |
   | `Gamma(3)` | 51840 | 24 | 45 | 21 | 5 | 1/15 |

   | `Gamma(2)` n stab. of a point of `P^3(F_3)` | 600 | 3 | 5 | 2 | 5 | 1/15 |
   | stab. of a nondegenerate plane mod 2 and mod 3 | 1800 | 3 | 10 | 7 | 10 | 1/30 |
   | stab. of a Lagrangian flag mod 2 and mod 3 | 7200 | 5 | 10 | 5 | 5 | 1/15 |
   | stab. of a point mod 3 and mod 5 | 6240 | 1 | 2 | 1 | 5 | 1/15 |

   The artifact files hold the full census: 22 subgroups of one level (levels 1, 2, 3, 4, 5, 7, 9) and 7
   intersections of stabilizers at levels 6 and 15, 29 subgroups in all. Every value found is `1/15` or `1/30`.
   In every case the gcd `g` of augmentations of `W` is `5` or `10`, and `d = 1/15` exactly when `g = 5`.

   *Level-three structure* (`gq24_check.py`, output `gq24-check-frame-3.json`). This is a computation, not
   used in the proof. The class of a coset of `Gamma(3)` depends only on the symplectic splitting
   `F_3^4 = P + P^perp` attached to it, and this gives a bijection from the 45 classes to the 45 splittings.
   Call two splittings transverse when all four intersections of their planes are zero. Then:
   - the transversality graph is 12-regular;
   - it has exactly 27 cliques of size 5, and each splitting lies in exactly 3 of them (the incidence pattern
     of lines and points of the generalized quadrangle `GQ(2,4)`);
   - the 27 clique indicator vectors ("point stars") lie in `W(Gamma(3))` and generate it over `Z`
     (rank 21, index 1).

   So `W(Gamma(3))` is exactly the lattice of `GQ(2,4)` point stars. Each star has augmentation 5 and
   `l1`-norm 5, and it is the certificate for `d(Gamma(3)) = 1/15`.
5. **(TA5) Consequences.**
   - `d_inf <= d(Gamma(2)) = 1/30`. So the Torelli-abelian gap is at most `2 sin(pi/30) = 0.2091`, and this
     value is attained by a monomial representation of `M` of degree `720`.
   - `d_inf > 0` is necessary for `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`.
     Therefore `d_inf = 0` would refute `deligne-triple-cover-exact-mf-radical`, by the "necessary for the
     flagship" argument recorded in that node.
   - The census exhibits no decay through level three: `d(Gamma(3)) = d(Sp_4(Z))`.
