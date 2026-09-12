# Heisenberg centre pairing and the rank-four frame live in a locally finite group

Lane `w4-heisenberg` (family R4), 2026-09-12. Target: the centre-pairing plan of
`research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md`, node
`heisenberg-centre-pairing-constrains-two-root-defect`.

**Outcome.** The centre-pairing tension cannot become a contradiction. Every input of the mechanism
lies in the unitriangular group `UT_3(R)`, or in `UT_3(R)` extended by the branch swap, and these
groups are locally finite. Their direct-limit regular representation is a genuine rank model that
realizes the free profile on every finite subgroup at once, and in it `rk(N_23 N_12) = 3/8`. The same
model shows that the four-index Cuntz assembly of `rank-four-isometry-relations-give-corner-cuntz-family`
cannot be derived from positive-root data: its conclusion would put a unital Leavitt family in a
corner of positive rank. Node: `unitriangular-data-cannot-assemble-corner-leavitt-families`.

## 1. The regular model of a locally finite group

Let `K` be a field of characteristic `p`, `R` a countable `K`-algebra (for instance
`R = L_K(1,2)` with `K` finite), `n >= 3`, and `UT_n(R) = { 1 + X : X strictly upper triangular }`.
For a finite group `Q` and `alpha` in `F_p[Q]` put `r_Q(alpha) = rank(lambda_Q(alpha)) / |Q|`, where
`lambda_Q` is left multiplication on `F_p[Q]` (the free profile of
`finite-subgroup-rank-data-cannot-force-two-root-identity`).

**Theorem 1.**
1. `UT_n(R)` is locally finite.
2. Let `L` be a countable locally finite group. There is a homomorphism `sigma_reg : L -> M^x`, with `M` a
   rank ultraproduct of matrix algebras over `F_p`, such that `rk(sigma_reg(alpha)) = r_Q(alpha)` for
   every finite subgroup `Q <= L` and every `alpha` in `F_p[Q]`.
3. `r` is invariant under isomorphisms of finite subgroups. In particular
   `r_(gQg^-1)(g alpha g^-1) = r_Q(alpha)` for every `g` in `GL_n(R)` with `gQg^-1 <= L`.
4. For `L >= UT_3(R)` and `D = (sigma_reg(x_23(1)) - 1)(sigma_reg(x_12(1)) - 1)`: `rk(D) = 3/8` when
   `p = 2`, and `rk(D) >= p^-3 > 0` for odd `p`.

*Proof.*
1. Take `g_1, ..., g_m` in `UT_n(R)` and `X_i = g_i - 1`. Products of `n` strictly upper triangular
   matrices vanish, so the `F_p`-span `B` of the products `X_(i_1) ... X_(i_k)`, `1 <= k < n`, is a
   finite-dimensional algebra with `B^n = 0`. `1 + B` is a group (`(1+b)^-1 = sum (-b)^k`), it
   contains every `g_i`, and it is finite. This is (FPR1)-(FPR3) of
   `finite-positive-root-fragments-have-marked-regular-models`.
2. Enumerate `L = {u_1, u_2, ...}` and let `P_k = <u_1, ..., u_k>`, an increasing chain of finite
   subgroups with union `L`. Put `M = prod_omega M_(|P_k|)(F_p)` modulo the rank-null ideal, and
   `sigma_k(g) = lambda_(P_k)(g)` for `g` in `P_k`, `1` otherwise. For `g, h` in `L`, eventually
   `g, h, gh` lie in `P_k`, where `sigma_k` is multiplicative, so `[sigma_k]` is a homomorphism. For
   `alpha` in `F_p[Q]` with `Q <= P_j` and `k >= j`, `F_p[P_k]` is a free left `F_p[Q]`-module of rank
   `[P_k : Q]`, so `rank lambda_(P_k)(alpha) = [P_k : Q] rank lambda_Q(alpha)` and the normalized rank
   is `r_Q(alpha)`.
3. A group isomorphism `Q -> Q'` induces an algebra isomorphism of group algebras that carries the
   regular module to the regular module.
4. `x_12(1)` and `x_23(1)` have order `p`, and their commutator `x_13(1)` is central of order `p`, so
   they generate the Heisenberg group over `F_p`, of order `p^3` (`D_8` for `p = 2`). For `p = 2`,
   with `a = x_12(1) - 1`, `b = x_23(1) - 1`, `c = x_13(1) - 1`, the monomials `a^i b^j c^k` form a basis
   and `ba = ab + c + ac + bc + abc`. The right ideal `ba F_2[D_8]` is spanned by `ba`, `bac = abc` and
   `bab = bc + abc`, so it has dimension `3` and `r = 3/8`, as on main. For odd `p` the four group
   elements in `(y-1)(x-1)` are distinct, so `lambda(alpha) != 0` and `r >= p^-3`.
QED

`sigma_reg` is a model of `L` only. It does not extend to `EL_n(R)`, and nothing here bears on
rank models of `R^x`.

## 2. The centre-pairing plan, input by input

Take `n = 3` and `L = UT_3(R) ⋊ <diag(w,w,w)>`, `w = s_0 t_1 + s_1 t_0`. The swap normalizes `UT_3(R)`
and has order `2`, so `L` is locally finite and Theorem 1 applies. Write `n_ab(c) = sigma_reg(x_ab(c)) - 1`.

* **Steinberg relations of `UT_3(R)` with any coefficients**, the Leavitt coefficients `s_i, t_j`
  jointly included. They are relations of `L`, so they hold. This covers the isometry commutator
  identities of `leavitt-isometry-commutators-constrain-el3-rank-models`.
* **Centre and pairing.** `n_13(c)` is central in `sigma_reg(UT_3(R))`, `n_13(c)^p = 0`, and
  `beta(a,b) = n_13(ab)` is the commutator pairing. All are group relations.
* **Bounded rank.** `rk n_13(c) = (p-1)/p` for `c != 0`, since `x_13(c)` has order `p`. The bounds
  `rk n_13(ab) <= rk N_13` and `rk n_13(ab) <= 2 rk N_23` hold with equal values on both sides.
* **Onto `R`.** `n_13(R)` is spanned by pairing values, trivially.
* **Rank values across positions.** A Weyl conjugation that carries a finite subgroup of `UT_3(R)`
  into `UT_3(R)` preserves `r` (Theorem 1.3).
* **Branch split and swap.** `x_12(1) = x_12(e_0) x_12(e_1)`, `P_i = n_23(e_i) n_12(e_i)`, and
  conjugation by `diag(w,w,w)` are relations and elements of `L`.
* **The hoped-for orthogonal chain.** For each word `v` in `{0,1}^k` put `e_v = s_v t_v`. The pair
  `x_12(e_v), x_23(e_v)` has commutator `x_13(e_v) != 1`, so it generates `D_8` (for `p = 2`), and
  `rk(n_23(e_v) n_12(e_v)) = 3/8` for all `2^k` words. For `k >= 2` these ranks sum to more than `1`, so
  the branch products are not independent, and nothing in the inputs forces them to be.

So every combination of these inputs holds in a model with `rk(N_23 N_12) = 3/8`. The mechanism
cannot prove the defect vanishes. The conclusion of the node, `N_23 N_12 = 0` for rank models of
`EL_3(R)`, is untouched: it is the gate `rank-models-of-el3-satisfy-the-two-root-identities`.

The prompt's calibration over `F_2[t]` or matrix rings is not needed. The Leavitt relations among
coefficients are invisible to `UT_3(R)`, because the regular model never produces a ring map on `R`.

## 3. Consequence for the rank-four assembly

`rank-four-isometry-relations-give-corner-cuntz-family` builds `S_0, S_1, T_0, T_1` and `e` from `EL_4`
positive-root data: `A_i = n_12(t_i)`, `B_j = n_23(s_j)`, `A'_i = n_23(t_i)`, `B'_j = n_34(s_j)`, the two
associator readings of `x_14(abc)`, and `1 + N_12 = (1 + n_12(e_0))(1 + n_12(e_1))`. All of this is
`sigma` restricted to `UT_4(R)`.

**Theorem 2.** No derivation of the following kind exists. From a rank model `sigma`, it forms `e`,
`S_i`, `T_j` by ring operations in `M` (sums, products, range projections, corners) applied to
`sigma(UT_4(R))`, and proves

* (a) `T_i S_j = delta_ij e`;
* (b) `S_0 T_0 + S_1 T_1 = e`;
* (c) `rk(e) = rk(N_23 N_12)`,

using only the relations of `UT_4(R)`, the ring structure of a rank ultraproduct, and rank
equalities between elements of `F_p[UT_4(R)]` related by isomorphisms of finite subgroups.

*Proof.* Apply the derivation to `sigma_reg` of `L = UT_4(R)`, where every input holds (Theorem 1).
By (c) and Theorem 1.4, `rk(e) > 0`. By (a), `S_0 T_0` and `S_1 T_1` are idempotents
(`(S_0 T_0)^2 = S_0 e T_0 = S_0 T_0`) and orthogonal (`S_0 T_0 S_1 T_1 = 0`). Also
`rk(S_i T_i) >= rk(T_i S_i T_i S_i) = rk(e)`. Ranks add over orthogonal idempotents, so (b) gives
`rk(e) >= 2 rk(e)`, hence `rk(e) = 0`, a contradiction. This is the argument of
`leavitt-algebra-has-no-unital-rank-model`, applied in the corner.
QED

**Remark (the weakened endpoint).** The family lead's pass and `w4-r4-approx` reduce the endpoint to
`T_0 S_0 = e = T_1 S_1`, `T_1 S_0 = 0`, and any positive lower bound on `rk(T_1)`. Since
`e = T_1 S_1`, that bound is the same as `rk(e) > 0`. Theorem 2 covers this endpoint too.

* **Idempotents.** `f_i = S_i T_i` is an idempotent in `eMe` with `rk(f_i) >= rk(e)`.
* **Orthogonality.** `f_1 f_0 = S_1 (T_1 S_0) T_0 = 0` is only one-sided, but `f'_0 = f_0 (e - f_1)` is
  again idempotent, since `f_1 f_0 = 0` gives `f'_0 f'_0 = f_0 (f_0 - f_1 f_0)(e - f_1) = f'_0`. It is
  orthogonal to `f_1` on both sides, and `rk(f'_0) = rk(f_0)` because `f'_0 f_0 = f_0`.
* **Contradiction.** `f'_0 + f_1` is an idempotent in `eMe`, so
  `rk(e) >= rk(f_0) + rk(f_1) >= 2 rk(e)`, and `rk(e) = 0`.

So in the regular model no positive-root derivation reaches even the weakened endpoint.

The same holds with `UT_4(R)` replaced by any sofic subgroup containing it: the permutation models of
`sofic-subgroups-carry-rank-models-violating-two-root-identity` have `rk(N_23 N_12) = 3/8`, and an
argument whose inputs are properties shared by all rank models of that subgroup would apply to them.
So at least one of (a)-(c) must use `sigma` as an operator on negative root elements or torus units,
jointly on a nonsofic subgroup. `tagged-a3-associator-cell-has-finite-positive-root-model` already
records a finite positive-root model of an `A_3` associator cell in another campaign. Theorem 2 is the
version that bears on the gate.

## 4. What a centre-pairing argument would have to use

* **Operators outside the unitriangular group.** It would need `sigma` as an operator on elements
  outside every sofic subgroup containing `x_12(1)` and `x_23(1)`. This is the requirement already
  recorded by `sofic-subgroups-carry-rank-models-violating-two-root-identity`; the plan adds nothing
  that meets it.
* **Torus units alone do not escape.** `UT_3(R) ⋊ T_0` has an amenable normal subgroup with quotient
  `T_0`, so it is sofic whenever `T_0` is sofic. That extension theorem is Elek–Szabó's, cited here and
  not re-derived. A torus subgroup of unknown soficity would be required.
* **Where the self-similarity sits.** The isomorphism `R ~= R^2` is not an element of `UT_3(R)`. Any
  element that implements it as an operator puts the argument on a larger subgroup, where
  Theorem 1 no longer applies. There the only known source of nonsofic subgroups of `R^x` is the
  nine-leaf compression configuration of the two-root artifact, Section 6.4.

So the centre-pairing plan has no `EL_3`-internal content beyond the gate itself.
