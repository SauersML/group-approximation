---
rg: 2
id: kms-hc1-iwahori-integral-h2-serre-plus-hc1
kind: claim
title: Integral H_2 of the Iwahori Lie ring is Serre plus Z/n at n*delta, with 3- and 2-torsion only; this decides the minimal relations of the pro-p Iwahori algebra for all p>=5 at once
distinct_from:
  kms-hc1-a2-iwahori-towers-deviate-only-at-kassel-degrees: that claim computes H_2(L_p) over F_p one prime at a time (p=3..23) and proves the deviation bound (B). This claim computes H_2 of the Z-form once, for all primes simultaneously, proves the reduction Open-1 <=> p-torsion of H_2(L_Z), and gives tower agreement uniformly in p (every p>=5, including all p>=29, for which no bound was recorded).
  kms-hc1-a2-pro-p-completion-is-iwahori-criterion: that claim is the criterion phi^ iso iff towers agree iff r(I_1)<=9. This claim supplies the integral Lie-algebra input for its tower condition, uniformly in p.
artifacts:
  - experiments/kms-hc1-iwahori-integral-h2-2026-09-17/h2z.py
  - experiments/kms-hc1-iwahori-integral-h2-2026-09-17/h2z90.out
  - experiments/kms-hc1-iwahori-integral-h2-2026-09-17/check_pattern.py
---

Notation as in `kms-hc1-a2-iwahori-towers-deviate-only-at-kassel-degrees`.
Let `L_Z = n^+(sl_3)_Z + t sl_3(Z[t])` be the Chevalley `Z`-form, with basis
`t^a E_ij` (`i != j`, `a >= 1` if `i > j`) and `t^a h_1, t^a h_2` (`a >= 1`),
`h_1 = E11-E22`, `h_2 = E22-E33`. So `L_p = L_Z (x) F_p` for every prime `p`.
`L_Z` is graded by the affine root lattice: `wt(t^a E_ij) = eps_i - eps_j + a delta`,
written in simple-root coordinates `(c_0,c_1,c_2)` with `delta = (1,1,1)`. The
p-central degree is `k = c_0+c_1+c_2`, so `delta` has degree 3.

- **(Z1) Generation and UCT.** `L_Z` is generated as a Lie ring by
  `E_12, E_23, tE_31` (every basis element of degree `>= 2` is a bracket of two
  lower basis elements with coefficient 1). Hence `H_1(L_Z) = Z^3`, free, and
  for every prime `p` and every weight `w`,

  ```text
  dim_{F_p} H_2(L_p)_w = rank H_2(L_Z)_w + #{invariant factors of Tors H_2(L_Z)_w divisible by p}.
  ```

- **(Z2) Computation (exact, over Z, every weight of degree <= 90).**

  ```text
  H_2(L_Z)_{deg<=90} = Z^6                        (the 6 weights of degree 3: Serre relations)
                     + sum_{n=2}^{30} Z/n          (weight n delta, degree 3n)
                     + sum_{n=2}^{30} (Z/3)^6      (weights n delta + alpha_i - alpha_j, i != j, degree 3n)
                     + (Z/2)^3                     (weights (1,2,2),(2,1,2),(2,2,1), degree 5)
  ```

  and nothing else. `h2z.py` computes the Smith normal forms of the
  Chevalley--Eilenberg differentials `d_2, d_3` weight by weight
  (python-flint `fmpz_mat`); `check_pattern.py` checks every weight line of
  `h2z90.out` against the display above (212 weights, 0 anomalies).
- **(Z3) Open 1 of the deviation claim, through degree 90, for every
  `p >= 5` at once.** By (Z1)+(Z2), for every prime `p >= 5`,
  `D_p cap [1,90] = {3} + {3mp <= 90}`, with `dim H_2(L_p)_3 = 6` and
  `dim H_2(L_p)_{3mp} = 1`. The 2- and 3-torsion is invisible for `p>=5`.
  This reproduces all the independent `F_p` computations of the deviation
  claim in their overlap (`p = 5,...,23`).
- **(Z4) p = 3 explained.** For `p = 3`, (Z1)+(Z2) give
  `dim H_2(L_3)_{3n} = 6 + [3 | n]` for `2 <= n <= 30`, i.e. `6,7,6,6,7,6,6,...`
  at degrees `6,9,12,15,18,21,24,...`, matching `h2_p3.out` of the deviation
  claim exactly. The six extra relations at degree 6 are the `(Z/3)^6` family
  at `2 delta + alpha_i - alpha_j`; they are the excess `8-2 = 6` at which the
  `p=3` tower (T3) of the criterion claim leaves the Iwahori pattern.
- **(Z5) Tower agreement uniform in p.** For every odd `p`,
  `gr_k(Gamma^) = gr_k(I_1)` for `k <= 3` (the degree-3 relations of `L_p` are
  exactly the six Serre relations, and they hold in `Gamma`). Feeding (Z3)
  into the deviation bound (B): for every prime `p >= 5`,

  ```text
  |Gamma^A2_p / P_k| = |I_1 / P_k|   for all k <= min(3p, 91).
  ```

  So every p-group image of `Gamma^A2_p` of p-class `<= 3p-1` (if `p <= 29`)
  or of p-class `<= 90` (if `p >= 31`) factors through `I_1` and kills `w_p`.
  Before, certified bounds were recorded only for `p = 5,7,11,13` (class
  59, 62, 65, 38); for every `p >= 29` nothing was recorded. The statement
  for all `p >= 31` needs no group computation at all.
- **(Z6) Reduction (both directions).** Open statement 1 of the deviation
  claim (`D_p = {3} + 3pN` with dimensions 6 and 1, for all `p >= 5`) is
  equivalent to the following single statement over `Z`:

  > for every prime `p >= 5` and every weight `w`, the number of invariant
  > factors of `Tors H_2(L_Z)_w` divisible by `p` is `1` if `w = n delta` with
  > `p | n`, and `0` otherwise.

  (The free part is `Z^6` in degree 3 by Garland--Lepowsky over `Q`.) The
  data in (Z2) suggest the sharper form
  `H_2(L_Z) (x) Z[1/6] = Z[1/6]^6 + sum_{n>=2} Z[1/6]/n`, i.e.
  Serre plus `HC_1` of the Iwahori order. Moreover, for `k >= 4`,
  `H_2(L_Z)_k = (J/[K,J])_k`, where `K = K_Z` is the Lie ring on
  `e_0,e_1,e_2` with the six Serre relations and `J = ker(K_Z -> L_Z)` is its
  torsion subgroup (Hopf formula; `K_Q = L_Q` by Gabber--Kac). So Open 1 is a
  statement about the torsion of the Kac--Moody Lie ring of type `A~2` over
  `Z`: its coinvariants are `Z/n` at `n delta` away from 6.

Scope. (Z1), (Z5) given (Z3), and the equivalence (Z6) are proofs. (Z2),
(Z3), (Z4) are exact finite certificates through degree 90. Not claimed:
the pattern of (Z2) in all degrees, and Open statement 2 (the Kassel
directions die in `Gamma^`). For `p >= 5` the first graded piece not decided
by (Z5) is `gr_{3p}` (a Kassel degree) when `p <= 29`, and `gr_91` when
`p >= 31`.

Proof: `kms-hc1-iwahori-integral-h2-serre-plus-hc1-proof`.
