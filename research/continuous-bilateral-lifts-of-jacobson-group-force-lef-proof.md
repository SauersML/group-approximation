---
rg: 2
id: continuous-bilateral-lifts-of-jacobson-group-force-lef-proof
kind: route
title: Proof that periodic points give LEF models of the bilateral affine topological full group, and that continuous lifts of EL_n(J) therefore contradict non-LEF
target: continuous-bilateral-lifts-of-jacobson-group-force-lef
requires:
  - cohn-elementary-group-is-not-lef
---

The notation is that of the target.
- Write `(z xi)_p = xi_(p-1)`, coordinatewise in each of the `N` components.
- For `R >= 0`, the *window* `xi|R` is the restriction of `xi` to positions `[-R, R]` in all `N` components.
- For `g = (w, lambda) in G_N`, the *radius* `rad(g)` is the least `D >= 0` such that `w` is supported in `[-D, D]`
  and every entry of `lambda` and of `lambda^(-1)` is a combination of `z^j` with `|j| <= D`.
  Then `(g xi)_p` depends only on `xi` at positions `[p - D, p + D]`.

## (C1) Free points, and uniqueness of cocycles

1. **Fixed sets are null.** Let `g = (w, lambda) != 1`.
   - If `lambda = 1`, then `w != 0` and `Fix(g) = {xi : xi + w = xi}` is empty.
   - If `lambda != 1`, then `Fix(g) = {xi : (lambda - 1) xi = w}` is empty or a coset of the closed subgroup
     `K = ker(lambda - 1)`.
2. **`K` has infinite index.** Pick an entry `a = (lambda - 1)_(ij) != 0`. Then `a = z^k a'`, where `a'` has
   nonzero constant term and nonzero top coefficient.
   - Multiplication by `a'` maps `F_2^Z` onto `F_2^Z`. Given `s`, put `t_0 = ... = t_(d-1) = 0`, where `d = deg a'`.
     Then solve `a' t = s` for the later coordinates by forward recursion, using the constant term, and for the
     earlier ones by backward recursion, using the top coefficient.
   - So the `i`-th coordinate of `(lambda - 1)(t e_j)` runs over all of `F_2^Z`. The image `(lambda - 1) X_N` is
     infinite.
   - As an abstract group, `X_N / K` is isomorphic to that image. So `[X_N : K] = infinity`.
3. **Consequence.** A closed subgroup of infinite index in a compact group has infinitely many disjoint translates,
   all of the same Haar measure. So it is Haar-null, and so is `Fix(g)`.
   - Every nonempty open set of `X_N` has positive measure, so `Fix(g)` is closed with empty interior.
   - `G_N` is countable. So `Free = X_N \ union_(g != 1) Fix(g)` is conull, and comeagre by Baire, hence dense.
4. **Uniqueness.** Let `h, h'` be continuous with `h(xi) xi = h'(xi) xi` for all `xi`.
   - At a free point, `h(xi) = h'(xi)`.
   - `{h = h'}` is clopen, because both maps are locally constant, and it contains the dense set `Free`. So
     `h = h'`.
5. **Cocycle identity.** For `phi, psi in [[G_N ~ X_N]]`, the map `xi -> h_phi(psi xi) h_psi(xi)` is continuous and
   is a cocycle for `phi psi`. By step 4 it equals `h_(phi psi)` everywhere.
   - In particular `h_id = 1`.
   - `[[G_N ~ X_N]]` is a group: the inverse of `phi` has the continuous cocycle
     `xi -> h_phi(phi^(-1) xi)^(-1)`.

## (C2) Periodized models

1. **The finite module.** `Per_m` is an `A`-submodule of `X_N`, because `A` is commutative. So every `lambda` in
   `SL_N(A)` preserves it.
   - `per_m : W -> Per_m` is `A`-linear and onto, with kernel `(z^m - 1) W`. So `Per_m ≅ (A/(z^m - 1))^N`, which has
     `2^(mN)` points.
   - `A`-linearity gives `per_m(lambda w) = lambda per_m(w)`.
2. **`pi_m` is a homomorphism.** Put `pi_m(w, lambda) xi = lambda xi + per_m(w)` on `Per_m`. Then
   `pi_m(g) pi_m(g') xi = lambda lambda' xi + per_m(w + lambda w') = pi_m(g g') xi`, since
   `(w, lambda)(w', lambda') = (w + lambda w', lambda lambda')`. Each `pi_m(g)` is a bijection of `Per_m`.
3. **Comparison with the true action.** For `xi in Per_m` and `g = (w, lambda)` with `rad(g) <= D`,
   `pi_m(g) xi - g xi = per_m(w) - w = sum_(k != 0) z^(km) w`.
   - This is supported in the union over `k != 0` of `[-D, D] + km`.
   - So `pi_m(g) xi` and `g xi` agree on the window of radius `R` whenever `m > R + D`.
4. **Constants.** Let `F ⊆ [[G_N ~ X_N]]` be finite.
   - By compactness each `h_phi` takes finitely many values. There is `R_F` such that `h_phi(xi)` depends only on
     `xi|R_F`, for all `phi in F`.
   - Let `D_F` be the maximal radius of a value of `h_phi` with `phi in F`.
5. **Multiplicativity.** Let `m > R_F + D_F`, `phi, psi in F` and `xi in Per_m`.
   - By step 3 applied to `g = h_psi(xi)`, the points `Phi_m(psi) xi = pi_m(h_psi(xi)) xi` and
     `psi xi = h_psi(xi) xi` agree on the window of radius `R_F`. So `h_phi(Phi_m(psi) xi) = h_phi(psi xi)`.
   - Hence, with `Phi_m(psi) xi in Per_m` by step 2:

     ```text
     Phi_m(phi) Phi_m(psi) xi = pi_m(h_phi(psi xi)) pi_m(h_psi(xi)) xi
                              = pi_m(h_phi(psi xi) h_psi(xi)) xi
                              = pi_m(h_(phi psi)(xi)) xi = Phi_m(phi psi) xi,
     ```

     using step 2 and the cocycle identity (C1.5), which holds at every point of `X_N`, including periodic ones.
   - In particular `Phi_m(1) = id`, since `h_1 = 1`. If `F` is symmetric, each `Phi_m(phi)` is a bijection with
     inverse `Phi_m(phi^(-1))`. In general `Phi_m(phi)` is a bijection for all large `m`: apply the above to
     `F ∪ F^(-1) ∪ {1}`.
6. **Injectivity.** Let `phi != phi'` in `F`.
   - There is a cylinder `U`, fixed by a window of radius `R_U`, on which `h_phi = g` and `h_(phi') = g'` are
     constant, and some `xi_0 in U` with `g xi_0 != g' xi_0`. Such a `U` exists because the set where `phi` and
     `phi'` differ is open and nonempty, and the cocycles are locally constant.
   - Put `k = g^(-1) g' = (u, mu)`. Then `k xi_0 != xi_0`, so `(k xi_0)_p != (xi_0)_p` at some position `p`, in some
     component.
   - Let `M = max(R_U, |p| + rad(k))` and `m > 2M + rad(k) + 1`.
   - Let `xi in Per_m` be the `m`-periodic point that agrees with `xi_0` on `[-M, M]`. It exists because
     `m > 2M + 1`. Then `xi in U`, and by step 3 (with `R = |p|`)
     `(pi_m(k) xi)_p = (k xi)_p = (k xi_0)_p != (xi_0)_p = xi_p`. The middle equality holds because `(k xi)_p`
     depends only on `xi` at positions `[p - rad(k), p + rad(k)] ⊆ [-M, M]`.
   - So `pi_m(k) xi != xi`, that is, `pi_m(g) xi != pi_m(g') xi`, that is, `Phi_m(phi) xi != Phi_m(phi') xi`.
   - Take `m` larger than these bounds for all of the finitely many pairs in `F`.

## (C3) LEF

Let `F` be finite and let `m` exceed all the bounds in (C2.5)–(C2.6) for `F ∪ F^(-1) ∪ {1}`. Then
`Phi_m : F -> Sym(Per_m)` is injective, and multiplicative on pairs from `F`. `Sym(Per_m)` is finite. This is the
definition of LEF for `[[G_N ~ X_N]]`, and LEF passes to subgroups.

## (C4) and (C5): continuous lifts

Let `alpha : Gamma -> [R'_N]` be an injective homomorphism from a group `Gamma` with symmetric generating set
`Sigma`. Suppose that for each `e in Sigma` the cocycle `h_e` of `alpha(e)` agrees `a.e.` with a continuous map
`c_e : X_N -> G_N`. We show that `Gamma` embeds in `[[G_N ~ X_N]]`.

1. **Each generator is a.e. a homeomorphism in the topological full group.** Put `phi_e(xi) = c_e(xi) xi`. It is
   continuous.
   - `alpha(e)` is measure-preserving. So `h_(e^(-1))(alpha(e) xi) = c_(e^(-1))(alpha(e) xi)` for a.e. `xi`, and
     `alpha(e) = phi_e` a.e.
   - Hence `phi_(e^(-1)) phi_e = alpha(e^(-1)) alpha(e) = id` a.e.
   - Continuous maps that agree a.e. agree on a dense set, hence everywhere, because the Haar measure has full
     support. So `phi_(e^(-1)) phi_e = id` everywhere, and likewise in the other order.
   - Thus `phi_e in [[G_N ~ X_N]]`.
2. **Every element is a.e. in the topological full group.** Every `gamma in Gamma` is a word `e_1 ... e_k` in
   `Sigma`. So `alpha(gamma) = alpha(e_1) ... alpha(e_k)`, which is a.e. equal to `phi_(e_1) ... phi_(e_k)`, an
   element of `[[G_N ~ X_N]]`.
   - This uses that each `alpha(e_i)` is measure-preserving, so a.e. equalities compose.
3. **The embedding.** Two elements of `[[G_N ~ X_N]]` that agree a.e. are equal, as in step 1.
   - So `alpha^c(gamma)` := the unique element of `[[G_N ~ X_N]]` a.e. equal to `alpha(gamma)` is well defined.
   - `alpha^c(gamma delta)` and `alpha^c(gamma) alpha^c(delta)` are both a.e. equal to `alpha(gamma delta)`, so they
     are equal.
   - If `alpha^c(gamma) = id`, then `alpha(gamma) = id` in `[R'_N]`, so `gamma = 1`.
   - So `alpha^c : Gamma -> [[G_N ~ X_N]]` is an injective homomorphism.
4. **Conclusion.** By (C3), `Gamma` is LEF.
   - **(C4).** Take `Gamma = E_n` with `n >= 4`. By `cohn-elementary-group-is-not-lef` it is not LEF, which is a
     contradiction. So some `h_e`, `e in Sigma`, is not a.e. equal to a continuous map.
   - **(C5).** Take `Gamma = E_3`. Then `E_3` is LEF, and LEF groups are sofic.

## Faithfulness of (ML) witnesses

This supports the application paragraph of the target and is not needed for (C1)–(C5).

1. Let `e -> e~` be an action of `E` on `(X_n, mu)` by elements of `[R'_n]` with `pr_+ o e~ = e o pr_+` a.e. Here
   `e` acts on `X_+ = (F_2^(Z>=0))^n` by the continuous extension of its action on `V = V_+^n`.
   - This extension exists because `S`, `T` and all of `J` act on `V_+` by maps that move each coordinate by a
     bounded amount.
2. If `e~ = id` a.e., then `e xi_+ = xi_+` for `pr_+`-a.e. `xi_+`, since `pr_+` pushes `mu` to Haar measure on
   `X_+`.
   - The action is continuous and Haar measure has full support, so `e` fixes `X_+` pointwise.
   - Then `e` fixes `V ⊆ X_+`, and `e = 1` because `E ≤ GL(V)`.
3. So `e -> e~` is an injective homomorphism `E -> [R'_n]`, and (C4) applies to it.

## Remarks

- The only place where continuity is used is (C2.5). There, `h_phi` must be evaluated at the periodized point
  `Phi_m(psi) xi` instead of at `psi xi`. The two points agree only on a window, so `h_phi` must depend only on
  a window. A merely measurable `h_phi` gives no control at the null set `Per_m`, and in fact the countable union of
  all `Per_m` is a null set. This is exactly why measurable lifts survive.
- (C3) is proved for the full affine group `G_N`, not for `SL_N(A)` alone. The periodization `per_m` of translation
  parts is what makes the non-periodic translates `lambda xi + w` usable. For the linear part alone, `Per_m` is
  invariant, and (C2) reduces to the residual finiteness of `SL_N(A)`.
