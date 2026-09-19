---
rg: 2
id: mod-s2-torelli-characters-have-a-metaplectic-maslov-line
kind: claim
title: The separating-twist count of commutator Torelli words in a finite-index subgroup of Mod(S_2) is 5m Z with m in {1,2} set by the metaplectic cover, so r = +-1/5 and exact Torelli-scalar values are exactly the tenth roots of unity
distinct_from:
  mod-s2-real-untwisting-identifies-deligne-norm-parameters: that proves the real untwisting f exists with f(t_s) = r = a/10 and 3 not dividing a, leaving r = +-1/5 as an unlanded heuristic; this pins r = +-1/5 and computes the separating-twist count of commutator Torelli words in every finite-index subgroup H = pi^-1(Gamma').
  deligne-torelli-character-counts-separating-twists: its (ST5) excludes the single scalar value omega for t_s; this determines the full set of exact scalar values, (1/10)Z/Z, attains each of them, and gives the sharp operator-norm distance 2 sin(pi/30) from the cube roots within that class.
  deligne-triple-cover-is-a-torelli-scalar-quotient-of-mod-s2: its (TS4) is the Z/3 invisibility of the Torelli character on Mod(S_2); this is an integral statement about F on K cap [H,H] for every finite-index H, with the index-two metaplectic dichotomy as the only freedom.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that asks for a uniform gap for all exact representations; this settles only the subclass where t_s is sent to a central element, and reduces the Torelli-abelian monomial subclass to the absence of small positive characters.
---

**ESTABLISHED** through `mod-s2-torelli-metaplectic-maslov-line-proof`. Unreviewed; no novelty claimed. One classical
input is used by citation (the braid group `B_3` as the universal-cover preimage of `SL_2(Z)`); see the route.

## Setting

- `M = Mod(S_2)`, `pi : M -> Gamma = Sp_4(Z)`, `K = ker pi` the Torelli group.
- `Gamma~` is the preimage of `Gamma` in the universal cover of `Sp_4(R)`, `z` is its central covering generator, and
  `E_2 = Gamma~/<z^2>` is the metaplectic double cover.
- `F : K -> Z` is the separating-twist count. By Mess, `K` is free on separating twists, one for each symplectic
  splitting, so `F(k)` is the total exponent of `k` in separating twists, and `F(t_s) = 1` for every separating twist.
- For a finite-index subgroup `Gamma' <= Gamma` put `H = pi^-1(Gamma')`, which contains `K`, and let `Gamma~'` be the
  preimage of `Gamma'` in `Gamma~`. Let `O = O(H)` be the finite set of `H`-conjugacy classes of separating twists (the
  `Gamma'`-orbits of splittings), and `nu : K -> Z^O` the orbit-count map, so `F = sum_o nu_o`.
- `L(H) = nu(K cap [H,H]) <= Z^O` is the *relation lattice* of `H`.
- The *metaplectic index* `m(Gamma')` is the order of the image of `z` in `H_1(Gamma~'; Z)`.
- `r = f(t_s)` is the separating-twist value of the unique real untwisting `f : M -> R` of
  `mod-s2-real-untwisting-identifies-deligne-norm-parameters`.
- The Torelli-abelian gap of `H` is
  ```text
  d(H) = inf over characters theta : H -> R/Z of  max over o in O of  || theta(t_o) - 1/3 ||_(R/Z).
  ```
  Here `t_o` is any twist in the class `o`. `d(H)` is the best operator-norm distance
  `||rho(t_s) - omega I||_op = 2 sin(pi d)` over monomial representations `rho = Ind_H^M theta`.

## Statement

1. **(ML1) Commutator Torelli words.** For every finite-index `Gamma' <= Gamma`,
   ```text
   F(K cap [H,H])  =  5 m(Gamma') Z,        m(Gamma') in {1, 2}.
   ```
   - `m(Gamma') = 2` iff `Gamma~'` has a character `chi` with `chi(z) = -1`, iff `z notin [Gamma~', Gamma~']`. This
     holds in particular when `E_2` splits over `Gamma'`.
   - `m` is monotone: `Gamma'' <= Gamma'` implies `m(Gamma'') >= m(Gamma')`.
   - `m(Sp_4(Z)) = 1`, and `m(Gamma') = 2` for some finite-index `Gamma'`, hence for a cofinal family.
   - Precisely: `z^n in [Gamma~', Gamma~']` iff `n = +-F(k)/5` for some `k in K cap [H,H]` (one sign, fixed by the
     orientation of `z`).
2. **(ML0) The untwisting value.** `r = +-1/5`, that is `a = 10 r = +-2`. This settles the heuristic in the remarks of
   `mod-s2-real-untwisting-deligne-norm-parameters-proof`. By Step 3 of that route, the mod-three Torelli character
   `h|_K` has `h(t_s) = a mod 3 = -+1`, so the unit `epsilon` of (ST2) is tied to the sign of `r`.
3. **(ML2) Maslov-line characters.** A character `theta : H -> R/Z` with `theta|_K = alpha F mod 1` exists iff
   `5 m(Gamma') alpha` is an integer. Choosing `alpha` in `(1/(5m))Z` nearest `1/3` gives
   ```text
   d(H)  <=  1/(15 m(Gamma')),     so d(H) <= 1/15 always, and d(H) <= 1/30 when m(Gamma') = 2.
   ```
   The corresponding `Ind_H^M theta` sends every separating twist to the scalar `exp(2 pi i alpha) I`.
4. **(ML3) Class kill: central separating twists.** Let `rho` be a finite-dimensional unitary representation of `M`
   such that `rho(t_s)` commutes with `rho(M)`; equivalently, all separating twists have the same image `U`. Then
   `U^10 = I`. So
   ```text
   || rho(t_s) - omega^(+-1) I ||_op  >=  2 sin(pi/30)  ~  0.2091.
   ```
   The bound is sharp, and every tenth root of unity is the exact scalar value of some representation. The invariant
   is the metaplectic index: the scalar lies in `(1/(5m))Z/Z`, and `m <= 2`. Every member dies at the same step,
   where `alpha F` must vanish on `K cap [H,H]`.
5. **(ML4) No positive real directions.** No homomorphism `v : H -> R` is positive on every separating twist. The
   transfer produces a relation vector
   `ell_T = 5 sum_(x in M/H) e_(o(x^-1 t_s x))` in `L(H)` with nonnegative entries and `F(ell_T) = 5[M:H]`.
6. **(ML5) Reduction of the census to small positive characters.** `d(H) < 1/(15m)` iff `H` has a character `psi` with
   ```text
   psi(t_o)  in  (0, 2/(15m))  mod 1   for every o in O.
   ```
   By (ML4), such a `psi` is never the reduction of a real character of `H`. If `L(H)` contains a nonnegative vector
   `ell` with `F(ell) = 5m`, then `d(H) = 1/(15m)` exactly.

## Reading

- **The census values are the Maslov line.** The w11 congruence census of Torelli-abelian characters found `d(H)` in
  `{1/15, 1/30}` on all 29 subgroups tested, with `d(Gamma(3)) = 1/15` and `d(Gamma(2)) = 1/30`. These are exactly
  the values `1/(15m)` of (ML2) for `m = 1, 2`. The characters that realize them are the scalar ones, so on every
  tested subgroup the extra Mess directions (characters off the Maslov line) gain nothing.
  - By (ML2), the census value `d(Gamma(3)) = 1/15` forces `m(Gamma(3)) = 1`: no character of `Gamma~(3)` sends
    `z` to `-1`.
  - `d(Gamma(2)) = 1/30` agrees with `m(Gamma(2)) = 2`. Classically the theta multiplier is a genuine character of the
    metaplectic preimage of the theta group, which contains `Gamma(2)`. That fact is not imported here.
- **Positivity of the census limit is now a single optimality statement.** By (ML2), `m <= 2` and monotonicity,
  `d_inf = inf_N d(Gamma(N)) <= 1/30`. It equals `1/30` iff the Maslov line is optimal on a cofinal family of
  congruence subgroups: `mod-s2-maslov-line-is-optimal-for-torelli-characters`. By (ML5), a counterexample must be a
  small *positive torsion* character, meaning `psi(t_o)` is in `(0, 2/(15m))` for every orbit. By (ML4), no
  continuous (real) Mess direction can do this. Any beat has to come from finite-order characters of `H` that are
  nontrivial on `K` off the Maslov line.
- **What kills and what survives.** Every representation in which `t_s` is central dies at `2 sin(pi/30)`, by (ML3). A
  representation that approaches `omega` must make separating twists non-central, and in the Torelli-abelian
  monomial class it must use a small positive torsion character. The lower bound available from the transfer vector
  alone is `d(H) >= 1/(15 [M:H])` when `3` does not divide `[M:H]`. It is not uniform, and it is empty when `3`
  divides `[M:H]`, as it does for `Gamma(3)`.

## What is not claimed

- Nothing is claimed about `d(H)` from below beyond the certificate criterion in (ML5). In particular
  `d_inf > 0` is not proved.
- No identification of `F` with an intersection number on the Siegel threefold (Humbert product divisor) is claimed.
  The relation `n = -+F/5` is proved algebraically.
- Representations with nonabelian Torelli image are untouched, except through (ML3).
