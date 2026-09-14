# Self-similarity and the two-root identity: exact splits and the rank-modelled calibration

Lane `gk-ri-selfsim` (family R), 2026-09-12. It supports the established claims
`el3-two-root-violation-splits-over-leavitt-branches` and
`rank-modelled-coefficients-violate-two-root-identities`, and the refuted shortcut
`dyadic-constant-el3-rank-models-satisfy-two-root-identity`. It builds on
`research/artifacts/el3-two-root-identities-2026-09-12.md` [TR] and
`research/artifacts/leavitt-isometry-commutator-relations-2026-09-12.md` [IC].

Target: `rank-models-of-el3-satisfy-the-two-root-identities` for `R = L_(F_2)(1,2)`, i.e.
`N_23 N_12 = 0` in every characteristic-two rank model of `EL_3(R) = R^x`.

## 0. Summary

* **Proposition 1 (defect factorization).** In characteristic two,
  `n_ik(ab) = n_ij(a) n_jk(b) + (1 + n_ij(a)) (n_jk(b) n_ij(a)) (1 + n_jk(b))`.
  So `rk(n_ik(ab) - n_ij(a) n_jk(b)) = rk(n_jk(b) n_ij(a))`.
* **Proposition 2 (branch split).** Over `R = L_K(1,2)`, `char K = 2`, the unit two-root product
  splits exactly over the orthogonal idempotents `e_i = s_i t_i` into two conjugate branch
  products plus one cross term.
* **Theorem 3 (rank-modelled calibration).** If a unital ring `T` has a unital ring homomorphism
  into a rank ultraproduct over a field of characteristic `p`, then `EL_3(T)` has a rank model
  with `rk(N_23 N_12) = 2/9`. This contains [TR] Claim C.
* **Corollary 4.** The dyadic constants `D = colim M_(2^k)(F_2)` inside `R` have a unital rank
  model, and every relation of the uniform self-similar tower holds in `EL_3(D)`. So no argument
  using only those relations proves the identity. A proof needs relations whose coefficient
  subring has no unital rank model, for example `D` together with one isometry pair `s_0, t_0`,
  which already generates `R`.

## 1. Notation

`sigma : EL_3(R) -> M^x` is a homomorphism, and `n_ab(c) = sigma(x_ab(c)) - 1`. In
characteristic two `x_ab(c)^2 = x_ab(2c) = 1`, so `n_ab(c)^2 = 0` and
`sigma(x_ab(c))^-1 = 1 + n_ab(c)`. Write `N_ab = n_ab(1)`.

## 2. Proposition 1 (defect factorization)

**Proposition 1.** Let `R`, `M` be rings with `2 = 0`. For distinct `i, j, k` and `a, b` in `R`,
with `X = n_ij(a)` and `Y = n_jk(b)`,

```text
n_ik(ab) = XY + (1 + X)(YX)(1 + Y).
```

*Proof.* `x_ik(ab) = [x_ij(a), x_jk(b)] = (1+X)(1+Y)(1+X)(1+Y)`, since inverses are the elements
themselves. [TR] Section 5 expands this as `1 + XY + YX + XYX + YXY + XYXY`. Also
`(1+X)(YX)(1+Y) = YX + XYX + YXY + XYXY`. QED

**Corollary 1.1.** In a rank ultraproduct, `1 + X` and `1 + Y` are units, so

```text
rk(n_ik(ab) - n_ij(a) n_jk(b)) = rk(n_jk(b) n_ij(a)) =: delta_ijk(a, b).
```

**Corollary 1.2 (invariance).** Take `R = L_(F_2)(1,2)`, where `GL_3(R) = EL_3(R)`
(`leavitt-gl-equals-el-and-perfect-unit-group`). Then `delta_ijk(a,b)` does not depend on the
distinct triple `(i,j,k)`. It is also unchanged under `(a,b) -> (u a v^-1, v b w^-1)` for units
`u, v, w` of `R`. Proof: conjugate `sigma` by permutation matrices, which have no signs in
characteristic two, and by `diag(u, v, w)`. Conjugation preserves rank.

## 3. Proposition 2 (branch split)

Let `R = L_K(1,2)`, `char K = 2`, `e_i = s_i t_i`, and put

```text
a_i = n_12(e_i),   b_i = n_23(e_i),   P_i = b_i a_i,   C = b_0 a_1 + b_1 a_0.
```

**Proposition 2.**

1. `a_0, b_0` commute with `a_1, b_1`, and `a_0 a_1 = a_1 a_0`, `b_0 b_1 = b_1 b_0`.
2. `N_12 = a_0 + a_1 + a_0 a_1` and `N_23 = b_0 + b_1 + b_0 b_1`.
3. The split:

   ```text
   N_23 N_12 = P_0 (1 + a_1 + b_1 + P_1) + P_1 (1 + a_0 + b_0) + C .
   ```

4. With `w = s_0 t_1 + s_1 t_0` and `W = diag(w, w, w)`, conjugation by `sigma(W)` fixes `N_12` and
   `N_23`. It swaps `a_0 <-> a_1`, `b_0 <-> b_1` and `P_0 <-> P_1`, and fixes `C`. Hence
   `rk P_0 = rk P_1`.
5. `P_i` is the unit two-root product of the branch model `sigma o iota_i`, where
   `iota_i(g) = s_i g t_i + (1 - e_i)` entrywise. So

   ```text
   delta(sigma) <= 2 delta(sigma o iota_0) + rk(C),     delta(sigma) = rk(N_23 N_12).
   ```

*Proof.*

1. The root subgroups are abelian. Also `[x_12(e_0), x_23(e_1)] = x_13(e_0 e_1) = 1` and
   `[x_12(e_1), x_23(e_0)] = x_13(e_1 e_0) = 1`.
2. `x_ab(1) = x_ab(e_0) x_ab(e_1)`, since `e_0 + e_1 = 1`.
3. Expand the nine products and move branch-one factors past branch-zero factors with (1):
   `b_0 a_0 = P_0`, `b_1 a_1 = P_1`, `b_0 a_0 a_1 = P_0 a_1`, `b_1 a_0 a_1 = P_1 a_0`,
   `b_0 b_1 a_0 = P_0 b_1`, `b_0 b_1 a_1 = P_1 b_0`, `b_0 b_1 a_0 a_1 = P_0 P_1`, and the two
   cross products `b_0 a_1`, `b_1 a_0`. Grouping gives the formula.
4. `w^2 = s_0 t_1 s_1 t_0 + s_1 t_0 s_0 t_1 = e_0 + e_1 = 1`, so `W` lies in
   `GL_3(R) = EL_3(R)`. `W x_ab(c) W^-1 = x_ab(w c w)`, with `w s_0 = s_1` and `t_0 w = t_1`, so
   `w e_0 w = e_1` and `w 1 w = 1`.
5. `iota_i` is an injective endomorphism of `GL_3(R)`, because `t_i s_i = 1`. It sends `x_ab(1)`
   to `x_ab(e_i)`. The bound is subadditivity of rank. QED

The cross term `C` is a sum of products of commuting unit root elements that are disjoint in
the block coordinates `R^3 = R^6`: `b_0 a_1` is `n_(2_0, 3_0) n_(1_1, 2_1)`.

## 4. Theorem 3 (rank-modelled calibration)

**Theorem 3.** Let `T` be a unital ring, `M_omega = prod_omega M_(n_i)(k) / d_omega` a rank
ultraproduct with `char k = p`, and `phi : T -> M_omega` a unital ring homomorphism. Then
`EL_3(T)` has a homomorphism `tau` into the unit group of a rank ultraproduct over `k` whose unit
root elements satisfy

```text
rk(N_23 N_12) = 2/9 .
```

*Proof.*

* **Natural model.** `nu = GL_3(phi) : GL_3(T) -> GL_3(M_omega)`, and
  `M_3(M_omega) = prod_omega M_(3 n_i)(k) / d_omega` is again a rank ultraproduct.
* **Tensor square.** Pick representatives `nu_i(g)` in `M_(3 n_i)(k)` and put
  `tau(g) = (nu_i(g) (x) nu_i(g))_i` in `prod_omega M_(9 n_i^2)(k) / d_omega`.
  * It is well defined: `A (x) A - A' (x) A' = (A - A') (x) A + A' (x) (A - A')` has normalized
    rank at most `2 rk(A - A')`.
  * It is multiplicative: `(AB) (x) (AB) = (A (x) A)(B (x) B)`.
* **The unit roots.** `phi(1) = 1`, so `tau(x_ab(1)) = (1 + E_ab) (x) (1 + E_ab)`, tensored with
  the identity. Then `N_ab = E_ab (x) 1 + 1 (x) E_ab + E_ab (x) E_ab`.
* **The product.** `E_23 E_12 = 0`, so every term containing it vanishes, and

  ```text
  N_23 N_12 = E_23 (x) E_12 + E_12 (x) E_23 .
  ```

  On `k^3 (x) k^3` this sends `e_3 (x) e_2` to `e_2 (x) e_1` and `e_2 (x) e_3` to `e_1 (x) e_2`,
  and kills the other basis vectors. Its rank is 2, and tensoring with the identity keeps the
  normalized rank `2/9`. QED

**Scope consequence.** Let `T` be a subring of `R`. Any argument deriving `N_23 N_12 = 0` from
relations among elements of `EL_3(T)`, plus the axioms of rank ultraproducts, applies to `tau`
and fails. So a proof must use relations whose coefficient subring has no unital homomorphism
into any rank ultraproduct of the characteristic.

[TR] Claim C is the case where `phi` factors through some `M_n(F_p)`. Theorem 3 also covers
coefficient rings with no finite-dimensional representation, such as the dyadic constants below.

## 5. Corollary 4 (the uniform self-similar tower)

Let `R = L_(F_2)(1,2)` and `D_k = span{ s_u t_v : |u| = |v| = k }`, with `s_u = s_(u_1)...s_(u_k)`
and `t_v = t_(v_k)...t_(v_1)`.

* **The constants.** `D_k ~= M_(2^k)(F_2)` with matrix units `s_u t_v`. From
  `s_0 t_0 + s_1 t_1 = 1`, `s_u t_v = sum_i s_(u i) t_(v i)`, so `D_k` sits unitally in `D_(k+1)`
  as `a -> a (x) I_2`. Put `D = union_k D_k`.
* **A rank model of D.** `phi(a) = (a (x) I_(2^(n-k)))_(n >= k)` for `a` in `D_k` is a unital
  ring homomorphism `D -> prod_omega M_(2^n)(F_2) / d_omega`.
* **The tower lives in EL_3(D).**
  * `e_i`, `1 - e_i` and `w` lie in `D_1`.
  * `iota_i` maps `EL_3(D)` into itself, since `s_i D_k t_i` lies in `D_(k+1)`.
  * `W` lies in `GL_3(D_1) = GL_6(F_2) = EL_3(D_1)`.
  * `x_ab(1) = iota_0(x_ab(1)) iota_1(x_ab(1))` holds in `EL_3(D)`.
  * The block coordinates `R^3 = R^(3 2^k)` restricted to constants identify `EL_3(D_k)` with
    `SL_(3 2^k)(F_2)`, which contains the `SL_3(F_2)` displacement counting of [TR] Section 5.

**Corollary 4.** `EL_3(D)` has a rank model with `rk(N_23 N_12) = 2/9`. So
`dyadic-constant-el3-rank-models-satisfy-two-root-identity` is false, and no argument built only
from the uniform tower (`iota_0`, `iota_1`, `W`, the doubling identity, constants of any depth)
proves the target.

**The minimal surviving input.** The subring generated by `D` and one isometry pair `s_0, t_0` is
all of `R`: `s_1 = w s_0` and `t_1 = t_0 w`. It has no rank model, since the image of
`s_0 t_0 + s_1 t_1 = 1` would give `1 + 1 = 1` after direct finiteness. The Toeplitz subring
`<s_0, t_0>` alone maps onto `F_2` and dies by [TR] Claim C. So the input a proof must use is
relations mixing constants with the root elements `x_ab(s_0)`, `x_ab(t_0)`: for example [IC]'s
`x_13(1) = [x_12(t_0), x_23(s_0)]` together with `W`.

## 6. Where self-similarity stops (Attempts material, not claims)

* **Upper bounds only.** Proposition 2(5) bounds `delta(sigma)` above through the branch model
  and the cross term. There is no lower bound. When commuting branches act on tensor factors,
  ranks do not add, and Theorem 3's natural tensor square is exactly such a model over `D`.
* **Support halving is not available.** If the fixed-ideal globality of
  `leavitt-rank-models-kazhdan-fixed-ideals-are-global` applies to the subgroup `iota_0(R^x)`
  (it contains an image of the nine-leaf configuration, and its normal closure is `R^x` by
  simplicity), then the branch model `sigma o iota_0` has the same fixed right ideal as `sigma`.
  So branches cannot live on half of the space. This was not re-derived here.
* **Next unit, open.** Proposition 1 with `(a, b) = (t_i, s_i)` and `(1, 1)` gives

  ```text
  rk( N_12 N_23 - n_12(t_i) n_23(s_i) ) <= delta(1,1) + delta(t_i, s_i),
  ```

  since both products equal `n_13(1)` up to their defects. A contracting bridge from
  `delta(1,1)` to `delta(t_i, s_i)`, using `W` and both isometry pairs, is the remaining
  self-similar idea. None is known.
