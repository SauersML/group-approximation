---
rg: 2
id: mod-s2-torelli-abelian-scalar-gap-census-proof
kind: route
title: Split a Torelli-abelian representation into Torelli characters, untwist each eigenspace on a finite-index subgroup by Malcev, and read the spectrum of the separating twist off an induced character; then compute the lattice distances by Reidemeister-Schreier
target: mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
artifacts:
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census.py
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/gq24_check.py
---

Notation as in the target. Input:
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`. Item 1 says `M` is finitely
  presented, item 2 says `H_1(M) = Z/10`, and item 4 gives the exact sequence `1 -> K -> M -> Sp_4(Z) -> 1`.

Standard facts used, not re-pinned:
- **(F1) Malcev.** A finitely generated subgroup of `GL_d(C)` is residually finite (A. I. Mal'cev,
  Mat. Sb. 8 (50) (1940), 405-422).
- **(F2)** A commuting family of unitaries on `C^n` is simultaneously diagonalizable.
- **(F3)** `T = R/Z` is a divisible abelian group. So every homomorphism from a subgroup of an abelian group
  `A` to `T` extends to `A`.
- **(F4)** `|exp(2 pi i x) - exp(2 pi i y)| = 2 sin(pi ||x - y||)`, and `2 sin(pi t)` increases on `[0, 1/2]`.

Import used only in (TA2):
- **[CSP]** The congruence subgroup property for `Sp_4(Z)`. H. Bass, J. Milnor, J.-P. Serre,
  Publ. Math. IHES 33 (1967), Theorem 14.1, as quoted in the source check of
  `sp4-finite-index-multiplier-lazard-whitehead-proof`: "the congruence subgroup conjecture holds for
  `Sp_2n`, `n >= 2`. It asserts `C^S(G_k) = {1}` unless `S` is totally imaginary." For `k = Q` and `S` the
  archimedean place, this says that every finite-index subgroup of `Sp_4(Z)` contains some `Gamma(N)`.

## Step 0: induced characters

Let `Gamma'` have finite index, `M' = pi^(-1)(Gamma')`, and let `psi : M' -> T` be a character. Realize
`Ind_(M')^M psi` on the functions `f : M -> C` with `f(m x) = psi(m) f(x)` for `m in M'`. Here `M` acts by
`(y . f)(x) = f(x y)`.
- Let `f_c` be the function supported on `M' g_c` with `f_c(g_c) = 1`. These form an orthonormal basis.
- For `k in K` we have `g_c k = (g_c k g_c^(-1)) g_c`, and `g_c k g_c^(-1)` lies in `K <= M'`. So
  `k . f_c = psi(g_c k g_c^(-1)) f_c`.
- So `Ind psi` is diagonal on `K` in this basis. It is Torelli-abelian, and
  ```text
  spec Ind psi (t_s) = { psi(g_c t_s g_c^(-1)) : c in X } .                    (0.1)
  ```
- For `m in M'`, `psi(m g t_s g^(-1) m^(-1)) = psi(g t_s g^(-1))`, and every `g in M` is some `m g_c`. So
  the set (0.1) equals `{ psi(g t_s g^(-1)) : g in M }`. Note that `g t_s g^(-1)` always lies in `K <= M'`.

**The torus dictionary.** Write `psi(g_c t_s g_c^(-1)) = exp(2 pi i theta_c)`. Then `psi` factors through
`H_1(M')`, so `sum_c w_c theta_c = 0` for every `w in W(Gamma')`. That is, `theta in W(Gamma')^perp`.

Conversely, let `theta in W(Gamma')^perp`.
- The rule `sum_c n_c v_c -> sum_c n_c theta_c` is a well-defined homomorphism from the subgroup
  `<v_c> <= H_1(M')` to `T`. It is well defined exactly because `theta` annihilates `W(Gamma')`.
- By (F3) it extends to `H_1(M')`, which gives a character `psi` of `M'` with the prescribed values.

Hence, by (0.1) and (F4),
```text
min_psi || Ind psi (t_s) - omega I ||_op = min_(theta in W^perp) max_c 2 sin(pi ||theta_c - 1/3||)
                                          = 2 sin(pi d(Gamma')) .                   (0.2)
```
This is the sharpness half of (TA1).

## Step 1: Torelli characters and their orbit (lower bound of TA1)

Let `rho : M -> U(n)` be Torelli-abelian.

**Splitting.** By (F2), `C^n = (+)_(chi in S) E_chi`, where `S` is a finite set of characters
`chi : K -> T`, `E_chi != 0`, and `rho(k) = chi(k)` on `E_chi`.

**The action of M.** For `g in M` put `(g.chi)(k) = chi(g^(-1) k g)`. If `v in E_chi`, then
`rho(k) rho(g) v = rho(g) rho(g^(-1) k g) v = (g.chi)(k) rho(g) v`, so `rho(g) E_chi = E_(g.chi)`.
- So `M` permutes the finite set `S`.
- The stabilizer `M_chi` has finite index.
- `M_chi` contains `K`: for `k' in K`, `chi(k'^(-1) k k') = chi(k)` because `T` is abelian.

**Spectrum.** On `E_(g.chi)` the twist acts as `(g.chi)(t_s) = chi(g^(-1) t_s g)`, and `g.chi in S` for all
`g`. So for any fixed `chi in S`,
```text
|| rho(t_s) - omega I ||_op  >=  max_(g in M) | chi(g t_s g^(-1)) - omega | .          (1.1)
```

## Step 2: untwisting one eigenspace on a finite-index subgroup

Fix `chi in S`, put `E = E_chi` and `d = dim E`.
- `rho_E(m) = rho(m)|_E` is a homomorphism `M_chi -> U(E)` with `rho_E(k) = chi(k) I` for `k in K`.
- Let `q : U(E) -> PU(E)` be the quotient by scalars. Then `sigma = q o rho_E` kills `K`, so its image
  `G = sigma(M_chi)` is a quotient of `Gamma_chi = pi(M_chi)`.
- `Gamma_chi` has finite index in `Sp_4(Z)`, which is finitely generated as a quotient of `M` ([HOM] items
  1 and 4). So `G` is finitely generated.

**Lifting.** `q` restricted to `SU(E)` is onto `PU(E)`, with kernel `mu_d I`. Let `G^` be the preimage of `G`
in `SU(E)`.
- `G^` is an extension of a finitely generated group by a finite one, so it is a finitely generated
  subgroup of `GL_d(C)`, hence residually finite by (F1).
- Choose a finite-index normal subgroup `N <= G^` missing each of the finitely many nontrivial elements of
  `mu_d I`. Then `q` is injective on `N`, and `q(N)` has finite index in `G`.

**The subgroup.** Put `M'' = sigma^(-1)(q(N))`. It has finite index in `M_chi`, it contains `K`, and so
`M'' = pi^(-1)(Gamma'')` with `Gamma'' = pi(M'')`.
- Define `sigma~ = (q|_N)^(-1) o sigma : M'' -> N`. This is a homomorphism with `sigma~(K) = 1`.
- For `m in M''`, `q(rho_E(m)) = q(sigma~(m))`, so `rho_E(m) = psi(m) sigma~(m)` with `psi(m) in T`.
- Since scalars are central, `psi(m m') sigma~(m m') = rho_E(m) rho_E(m') = psi(m) psi(m') sigma~(m m')`. So
  `psi` is a character of `M''`.
- `psi|_K = chi`, because `sigma~(k) = I`.

**Conclusion.**
- By Step 0 applied to `Gamma''` and `psi`, the values `chi(g t_s g^(-1)) = psi(g t_s g^(-1))`, `g in M`, are
  the numbers `exp(2 pi i theta_c)` for some `theta in W(Gamma'')^perp`.
- So by (1.1) and (F4),
  `||rho(t_s) - omega I|| >= 2 sin(pi max_c ||theta_c - 1/3||) >= 2 sin(pi d(Gamma'')) >= 2 sin(pi d_inf)`.
- The last step uses `d_inf <= d(Gamma'') <= 1/3` and the monotonicity in (F4).

**The other cube root.** `W^perp` is a subgroup, so `-theta in W^perp`, and
`||theta_c - 2/3|| = ||(-theta_c) - 1/3||`. The same bound therefore holds for `omega^(-1)`. Together with
(0.2), this proves (TA1).

## Step 3: monotonicity and the congruence form (TA2)

Let `Gamma'' <= Gamma'` have finite index, and let `theta' in W(Gamma')^perp` attain `d(Gamma')`.
- Step 0 gives a character `psi'` of `M'` realizing `theta'`.
- Its restriction to `M'' <= M'` is a character of `M''`. By the last bullet of Step 0, its values on
  `{g t_s g^(-1) : g in M}` form the same set.
- So the corresponding `theta'' in W(Gamma'')^perp` has `max ||theta''_e - 1/3|| = d(Gamma')`, and
  `d(Gamma'') <= d(Gamma')`.

By [CSP], every finite-index `Gamma'` contains some `Gamma(N)`, so `d_inf = inf_N d(Gamma(N))`. If `N | N'`,
then `Gamma(N') <= Gamma(N)`. So `N -> d(Gamma(N))` is non-increasing on the directed set of levels, and its
infimum is its limit.

## Step 4: certificates (TA3)

Let `theta in W^perp` and `w in W` with `a = sum_c w_c` prime to `3`.
- Lift each `theta_c` to a real `t_c` with `|t_c - 1/3| = ||theta_c - 1/3|| =: e_c`.
- Then `sum_c w_c t_c` is an integer, and `sum_c w_c t_c = a/3 + sum_c w_c (t_c - 1/3)`.
- So `1/3 = ||a/3|| <= sum_c |w_c| e_c <= ||w||_1 max_c e_c`.

Since the coordinates with equal `v_c` are forced equal on `W^perp` (their difference lies in `W`), everything
can be computed on classes, i.e. on the distinct values of `v_c`.

## Step 5: the census (TA4)

**Algorithm** (`census.py`). The script is exact integer arithmetic, except for the two MILP searches, whose
outputs are re-verified exactly.
1. *Presentation.* The generators are `a_1, ..., a_5` on the Humphries chain. The relators are:
   - the braid and far-commutation relations;
   - `(a_1 ... a_5)^6 = 1`;
   - `iota^2 = 1` with `iota = a_1 a_2 a_3 a_4 a_5 a_5 a_4 a_3 a_2 a_1`;
   - `[iota, a_i] = 1`.

   They map to `Sp_4(Z)` by the transvections of the classes `b_1, a_1, b_1+b_2, a_2, b_2`. The script
   asserts that every relator holds there, that `iota -> -I`, and that `t_s = (a_1 a_2)^6 -> I`.
2. *Cosets.* `Gamma'` is the stabilizer of a finite object: a vector, a subspace or a frame mod `N`, a theta
   characteristic, or a tuple of these (an intersection of stabilizers). Orbit enumeration gives the
   permutation action on `X`. The script checks that each relator acts trivially and that `t_s` fixes every
   coset.
3. *Reidemeister-Schreier.* A BFS tree gives the Schreier generators. Each relator, read from each coset,
   gives a relation row. `v_c` is the rewrite of `t_s` read from coset `c`, which equals the rewrite of
   `u_c t_s u_c^(-1)` for the tree word `u_c`.
   - Then: exact elimination of generators on `+-1` pivots, an HNF over `Z` (python-flint), and the Smith
     invariants of `H_1(M')`.
   - `W` is read from the HNF of the block matrix `[[R, 0], [V, I]]`: the rows with vanishing first block
     form a basis of `W`.
4. *Distance.* A MILP proposes a feasible `theta` (as `h` with `B h in Z^r`, `B` a basis of `W`). It is then
   projected exactly over `Q` onto the proposed affine lattice coset `{B h = n}`. The script asserts
   `B h = n` exactly and reports the exact `max |h_c - 1/3|`, which is a rigorous upper bound on `d`.
5. *Certificate.* A MILP proposes `w = B^T y` of minimal `l1` norm with `sum w = 3q + 1`. The script checks
   the augmentation mod 3 exactly. By (TA3), `1/(3 ||w||_1)` is a rigorous lower bound.

In every listed case the two bounds coincide, so the value of `d` is exact.

**Sanity checks.**
- For `Gamma' = Sp_4(Z)` the script returns `H_1(M) = Z/10`, which agrees with [HOM] item 2.
- `W(Sp_4(Z)) = 5Z`, since `[t_s] = 12 [a_1] = 2` has order `5` in `Z/10`. Hence `d(Sp_4(Z)) = 1/15`:
  `theta = 2/5` is the Sp4-level character, at distance `1/15` from `1/3`.
- For `Gamma(2)` there are 10 classes, each of 72 cosets. This matches the 10 symplectic splittings of
  `F_2^4`, permuted transitively by `Sp_4(F_2)`. `W` is spanned by the all-ones vector, so `d = 1/30`,
  attained at `theta = 3/10` constant (then `10 theta = 0`).

**Trust surface.**
- *Lower bounds* (certificates) need only that every relator in item 1 holds in `M` and that `a_1..a_5`
  generate `M`. Both are standard (Humphries generators, braid and chain relations, and the hyperelliptic
  involution in genus two).
  - The reason: the presented group `G` then maps onto `M`. The preimage `G'` of `Gamma'` maps onto `M'`,
    so `H_1(G') -> H_1(M')` is onto and sends `v_c` to `v_c`. Hence `W_G <= W_M`, and every certificate
    found is valid for `M`.
- *Upper bounds* (exact feasible points, hence the values `d(Gamma(2)) = 1/30` and `d_inf <= 1/30`) use,
  in addition, that item 1 is a complete presentation of `M`. This is the Birman-Hilden presentation. It is
  cross-checked here only through `H_1 = Z/10`; the primary source was not re-read.
- Runtime: `Gamma(3)` (index 51840, 207361 Schreier generators, 29 after elimination) takes about 15 min and
  8 GB.

## Step 6: consequences (TA5)

- `d_inf <= d(Gamma(2)) = 1/30` by the definition of `d_inf`. The representation `Ind psi`, with `psi` the
  `Gamma(2)` optimum, has degree `[M : M_2] = 720` and is at distance `2 sin(pi/30)` by (0.2).
- **Necessity.** Suppose `d_inf = 0`. Then by (TA1) there are Torelli-abelian `rho` with
  `||rho(t_s) - omega I|| -> 0`. That contradicts `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`,
  which is therefore false, and by its "Position in the graph" `1/3 in P_op` and the flagship fails.
- This is recorded as a logical relation and not as a graph edge, to keep the graph acyclic.
