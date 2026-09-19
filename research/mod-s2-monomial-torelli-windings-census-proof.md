---
rg: 2
id: mod-s2-monomial-torelli-windings-census-proof
kind: route
title: Split a Torelli-abelian representation into Torelli characters, untwist one eigenspace on a finite-index subgroup by Malcev, write the trace-log of the separating twist as an induced-character sum, and bound it by short relations in H_1 of congruence preimages
target: mod-s2-monomial-torelli-windings-census
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
artifacts:
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings.py
  - experiments/mod-s2-near-identity-windings-2026-09-17/census.py
---

Notation as in the target. Input:
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`: item 1, `M` is finitely presented;
  item 2, `H_1(M) = Z/10`; item 4, the exact sequence `1 -> K -> M -> Sp_4(Z) -> 1`.

Standard facts, not re-pinned:
- **(F1) Malcev.** A finitely generated subgroup of `GL_d(C)` is residually finite (A. I. Mal'cev, Mat. Sb.
  8 (50) (1940), 405-422).
- **(F2)** A commuting family of unitaries is simultaneously diagonalizable.
- **(F3)** `T = R/Z` is divisible, so a character of a subgroup of an abelian group extends.
- **(F4)** `|exp(2 pi i x) - 1| = 2 sin(pi |x|)` for `|x| <= 1/2`, increasing in `|x|`.
- **[CSP]** (only for the congruence form in (MW2)) Every finite-index subgroup of `Sp_4(Z)` contains some
  `Gamma(N)`: H. Bass, J. Milnor, J.-P. Serre, Publ. Math. IHES 33 (1967), Theorem 14.1 ("the congruence
  subgroup conjecture holds for `Sp_2n`, `n >= 2`").

Steps 0 and 2 below are the same untwisting argument as in the w11 census route
`mod-s2-torelli-abelian-scalar-gap-census-proof` (swarm-0917, not in this worktree); they are written out
in full here so that this route depends only on [HOM] and the standard facts.

## Step 0: induced characters and their windings

Let `Gamma'` have finite index, `M' = pi^(-1)(Gamma')`, and `psi : M' -> T` a character. Realize
`Ind psi` on `f : M -> C` with `f(m x) = psi(m) f(x)` (`m in M'`), `M` acting by right translation.
- The functions `f_c` supported on `M' g_c` with `f_c(g_c) = 1` are an orthonormal basis, and for `k in K`,
  `k . f_c = psi(g_c k g_c^(-1)) f_c`, because `g_c k g_c^(-1) in K <= M'`.
- So `Ind psi (t_s)` is diagonal with eigenvalues `exp(2 pi i theta_c)`, `theta_c = psi(v_c)`, where
  `v_c = [g_c t_s g_c^(-1)] in H_1(M')`.
- Let `h_c in (-1/2, 1/2]` be the principal lift of `theta_c`. Then, whenever `max |h_c| < 1/2`,
  ```text
  || Ind psi (t_s) - 1 || = 2 sin(pi max_c |h_c|),      kappa(Ind psi (t_s)) = sum_c h_c .      (0.1)
  ```
- Group the cosets by the value of `v_c` (classes `j`, multiplicities `mult_j`). Then
  `kappa = sum_j mult_j h_j`.

**Torus dictionary.** `psi` factors through `H_1(M')`, so `sum_j w_j theta_j = 0` in `T` for all `w in W`.
Hence `sum_j w_j h_j in Z`, i.e. `h in W^*`. Conversely, if `h in R^classes` has `B h in Z^r` (`B` a basis of
`W`), then `sum_j n_j v_j -> sum_j n_j h_j mod 1` is well defined on `<v_j> <= H_1(M')`, extends to `H_1(M')`
by (F3), and gives a character `psi` with `psi(v_j) = h_j mod 1`. So the vectors `h` realized by characters of
`M'` (after principal lifting, when `max |h_j| < 1/2`) are exactly the `h in W^*` with `max |h_j| < 1/2`.

## Step 1: the winding is fifth-integral, and e is attained

**Transfer.** `t_s = (a_1 a_2)^6` and the Humphries generators are pairwise conjugate, so by [HOM] item 2
`t_s` maps to `12 = 2` in `H_1(M) = Z/10`, and `5 [t_s] = 0`. Every coset is fixed by `t_s in K`, so the
transfer `V : H_1(M) -> H_1(M')` sends `[t_s]` to `sum_c v_c = sum_j mult_j v_j`. Hence `5 mult in W`, and
```text
kappa(Ind psi (t_s)) = <mult, h>  in  (1/5) Z      for every h in W^* .            (1.1)
```
(The script computes the exact order `q | 5` of `mult` modulo `W`; `q = 1` in most cases, so there the winding is
an integer.)

**Attainment.** The set `F = { h in W^* : max |h_j| <= 1/2, <mult, h> >= 1/q }` is a finite union of compact
polytopes (only finitely many integer vectors `B h` occur for bounded `h`), and it is nonempty when `e < 1/2`.
By `h -> -h`, `e(Gamma') = min_F max_j |h_j|`, a minimum. If `e(Gamma') < 1/2`, a minimizer is realized by a
character `psi` (Step 0), and by (0.1) `Ind psi` has `||Ind psi(t_s) - 1|| = 2 sin(pi e(Gamma'))` and nonzero
winding. This is the sharpness half of (MW1).

**Per-level floor.** From (1.1), `max |h_j| < 1/(5 ||mult||_1)` forces `|kappa| < 1/5`, hence `kappa = 0`. So
`e(Gamma') >= 1/(5 [Gamma : Gamma'])` for every level. This is the non-uniform floor already recorded in the
w10 attempt on `mod-s2-near-identity-torelli-windings-vanish`; it is not used below.

## Step 2: a Torelli-abelian representation is a sum of induced-character windings (MW1)

Let `rho : M -> U(n)` be Torelli-abelian with `||rho(t_s) - 1|| < 2 sin(pi e_inf)`; in particular every
eigenvalue of `rho(t_s)` is `exp(2 pi i x)` with `|x| < e_inf <= 1/5`.

**Splitting.** By (F2), `C^n = (+)_(chi in S) E_chi` over a finite set `S` of characters of `K`, with
`rho(k) = chi(k)` on `E_chi`. As `rho(g) E_chi = E_(g.chi)`, where `(g.chi)(k) = chi(g^(-1) k g)`, `M`
permutes `S`, orbits are finite, stabilizers `M_chi` have finite index and contain `K`, and
`dim E_(g.chi) = dim E_chi`. On `E_(g.chi)` the twist is the scalar `chi(g^(-1) t_s g)`. So
```text
kappa(rho(t_s)) = sum_(orbits O) dim E_chi(O) * sum_(g in M/M_chi) hat(chi(g^(-1) t_s g)) ,      (2.1)
```
where `hat` is the principal lift and `chi(O)` is any point of `O`.

**Untwisting.** Fix `chi`, `E = E_chi`, `d = dim E`, `rho_E = rho|_E` on `M_chi`, and `q : U(E) -> PU(E)`.
- `sigma = q o rho_E` kills `K`, so `G = sigma(M_chi)` is a quotient of the finitely generated group
  `pi(M_chi)` ([HOM] items 1 and 4).
- Its preimage `G^` in `SU(E)` is finitely generated (an extension of `G` by `mu_d`), hence residually finite by
  (F1). Pick a finite-index normal `N <= G^` avoiding the nontrivial elements of `mu_d I`; then `q|_N` is
  injective with image of finite index in `G`.
- `M'' = sigma^(-1)(q(N))` has finite index in `M_chi` and contains `K`, so `M'' = pi^(-1)(Gamma'')`.
- `sigma~ = (q|_N)^(-1) o sigma : M'' -> N` is a homomorphism killing `K`, and `rho_E(m) = psi(m) sigma~(m)`
  defines a character `psi` of `M''` (scalars are central) with `psi|_K = chi`.

**Conclusion.** Let `j = [M_chi : M'']`. Coset sums over `M/M''` are `j` times coset sums over `M/M_chi`,
because `chi(g^(-1) t_s g)` depends only on the left coset `g M_chi` (for `m in M_chi`,
`chi(m^(-1) x m) = (m . chi)(x) = chi(x)`), and the left cosets `g M''` correspond to the right cosets
`M'' g_c` of Step 0 by `g = g_c^(-1)`, which turns `g^(-1) t_s g` into `g_c t_s g_c^(-1)`. So the inner sum in (2.1) is
`(1/j) kappa(Ind_(M'')^M psi (t_s))`, and by Step 0 the principal lifts of the values of `psi` on the `v_c` of
`Gamma''` form a vector `h in W(Gamma'')^*` with `max |h| < e_inf <= e(Gamma'')`. By the definition of
`e(Gamma'')` and (1.1), `<mult, h> = 0`. Hence every orbit contributes `0` to (2.1), and `kappa(rho(t_s)) = 0`.

## Step 3: monotonicity and the congruence form (MW2)

Let `Gamma'' <= Gamma'` have finite index and let `psi'` be a character of `M'` attaining `e(Gamma')` (Step 1).
Its restriction to `M''` is a character whose values on `{g t_s g^(-1) : g in M}` are the same set, and its
induced winding is `[M' : M''] kappa(Ind psi') != 0`. So `e(Gamma'') <= e(Gamma')`. With [CSP],
`e_inf = inf_N e(Gamma(N))`, a limit along levels ordered by divisibility.

## Step 4: certificates (MW3)

Let `w_1, ..., w_k in W` with `||w_i||_1 <= L` and `mult = sum_i a_i w_i`, `a_i in Q`. If `h in W^*` and
`max |h_j| < 1/L`, then each `<w_i, h>` is an integer of absolute value `< 1`, hence `0`, so `<mult, h> = 0`.
Thus `e(Gamma') >= 1/L`. Equal `v_c` give equal coordinates on `W^*`, so everything is computed on classes.

## Step 5: the computation (MW4)

`windings.py` imports `census.py` (an unchanged copy of the w11 census library: Birman-Hilden presentation on
the Humphries chain, `Sp_4` action on level structures, abelianized Reidemeister-Schreier, Hermite normal forms)
and, for each case:
- computes `H_1(M')`, the class vectors `v_j`, `mult`, a basis `B` of `W` and the order `q` of `mult` mod `W`;
- solves the MILP `min t : B h = n in Z^r, |h_j| <= t, <mult, h> >= 1/q`, then projects the float optimum
  exactly onto `B h = n` over `Q` and records the exact rational `max |h_j|` and `kappa` (an exact upper
  bound, realized by Step 1);
- searches short vectors of `W` (an LLL basis, its pairwise sums and differences, and all combinations with
  coefficients in `[-3, 3]` when `rank W <= 5`), and records the least `L` such that those of `l1`-norm at
  most `L` span a space containing `mult` (an exact lower bound `1/L` by Step 4); when this `L` exceeds
  `1/e_upper`, it retries at `L = 1/e_upper` by a greedy integer program that repeatedly asks for `w in W` with
  `||w||_1 <= L` and `<u, w> >= 1`, `u` the component of `mult` orthogonal to the vectors found so far. Each
  returned vector is re-checked in exact integer arithmetic (norm and membership in `W`), and the final span
  test is an exact rank computation, so the solver only proposes vectors.
A value in the target's table is marked exact when the two bounds agree. Everything used as proof is exact
integer or rational arithmetic; the MILP only proposes the point.
