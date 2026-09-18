---
rg: 2
id: deligne-parameter-group-is-a-virtual-invariant-proof
kind: route
title: Restrict and twisted-induce parameter models, then read the divisibility of the Maslov class off Deligne's residual
target: deligne-parameter-group-is-a-virtual-invariant
requires: [deligne-sep7-norm-parameter-closed-subgroup, deligne-covers-of-sp2g-z-have-finite-residual-2z, metaplectic-half-class-has-an-exact-finite-model]
---

Notation of the target. All cocycles are normalized: `beta(e,g) = beta(g,e) = 0`. `c^beta_theta` denotes
`exp(2 pi i theta beta)`. "Model" means an operator-norm asymptotic model as in the target. `Gamma` is finitely
presented, and so is every finite-index subgroup. So `H^2(Gamma';Z)` is finitely generated, and its torsion
subgroup `Tors` is finite.

**(V0) Only the class matters.**
- *Integral coboundaries.* Let `beta' = beta + delta nu` with `nu : L -> Z`. Normalization of `beta` and `beta'`
  gives `0 = (delta nu)(e,e) = nu(e)`. Put
  `u(g) = exp(2 pi i theta nu(g))`. Then `u(g)u(h)/u(gh) = c^(delta nu)_theta(g,h)`. So
  `U_n -> u U_n` turns a `c^beta_theta`-model into a `c^(beta')_theta`-model with the same defects, and `u(e) = 1`.
- *Torsion.* Let `tau` be an integral cocycle with `s tau = delta mu` for some `s >= 1` and integral `mu`. Put
  `v(g) = exp(2 pi i theta mu(g)/s)`. Then `v(g)v(h)/v(gh) = exp(2 pi i theta tau(g,h))`. So `c^tau_theta` is a
  multiplicative coboundary for every `theta`, and multiplying by `v` absorbs it, again with the same defects.
  If `v(e) != 1`, replace `U_n(e)` by `I`. Normalization gives `U_n(e)^2 - U_n(e) -> 0` with `U_n(e)` unitary, so
  `U_n(e) -> I` and the defects stay `o(1)`.
- Hence `P(L, beta)` depends only on `[beta]`, and `P(L, beta + tau) = P(L, beta)` for torsion `tau`.

**(V1) Finite-index invariance.**
- *Restriction.* A model for `(Gamma, b)` restricts to a model for `(Gamma', b|Gamma')`. So
  `P_op <= P(Gamma', b|Gamma')`.
- *Twisted induction.*
  - Setup. Let `r = [Gamma:Gamma']` and choose left-coset representatives `t_1 = e, t_2, ..., t_r`. For `g` in
    `Gamma` and each `j`, write `g t_j = t_(sigma_g j) h_j(g)` with `h_j(g)` in `Gamma'`. Then `sigma` is the
    action on `Gamma/Gamma'`, and `h_j(gk) = h_(sigma_k j)(g) h_j(k)`. Write `c = c^b_theta` and
    `lambda_j(g) = c(g, t_j) / c(t_(sigma_g j), h_j(g))`.
  - Construction. Given `U : Gamma' -> U(d)` with `U(e) = I`, define `V : Gamma -> U(C^r (x) C^d)` by

    ```text
    V(g)(e_j (x) v) = e_(sigma_g j) (x) lambda_j(g) U(h_j(g)) v.
    ```

    `V(g)` is unitary, since it is a block permutation with unitary blocks. `V(e) = I`, because `sigma_e = id`,
    `h_j(e) = e` and `lambda_j(e) = c(e,t_j)/c(t_j,e) = 1`.
  - *Exact scalar identity.* Put `h = h_j(k)` and `h' = h_(sigma_k j)(g)`. Then

    ```text
    lambda_(sigma_k j)(g) lambda_j(k) c(h', h) = c(g, k) lambda_j(gk).          (*)
    ```

    Proof. The twisted group algebra `A = C^c[Gamma]` has basis `u_g` and `u_g u_k = c(g,k) u_(gk)`. It is
    associative because `b` is a cocycle. It is a free right `A' = C^c[Gamma']`-module on `u_(t_1), ..., u_(t_r)`,
    since `u_(t_j h) = c(t_j,h)^(-1) u_(t_j) u_h`. Take the left regular module `A'` and form
    `M = A (x)_(A') A'`, which is `A` itself. The computation
    `u_g u_(t_j) = c(g,t_j) u_(t_(sigma_g j) h_j(g)) = lambda_j(g) u_(t_(sigma_g j)) u_(h_j(g))`
    shows that `u_g` acts on the basis `u_(t_j) u_x` exactly by the formula for `V`, with `U` the left regular
    `c|Gamma'`-action `u_x -> u_h u_x = c(h,x) u_(hx)`. Now compare `u_g (u_k (u_(t_j) u_e))` with
    `c(g,k) u_(gk) (u_(t_j) u_e)` using associativity. Both are scalar multiples of the basis vector
    `u_(t_(sigma_(gk) j)) u_(h' h)`. The scalars are the two sides of `(*)`.
  - *Defect.* By `(*)`, for every `j`,

    ```text
    (V(g)V(k) - c(g,k)V(gk))(e_j (x) v)
      = e_(sigma_(gk) j) (x) lambda_(sigma_k j)(g) lambda_j(k) (U(h')U(h) - c(h',h)U(h'h)) v.
    ```

    Here `c(h',h)` is `c^(b|Gamma')_theta(h',h)`. The operator `V(g)V(k) - c(g,k)V(gk)` maps the `j`-th block
    summand into the `sigma_(gk) j`-th, and `sigma_(gk)` is a bijection. So its norm is the maximum over `j` of the
    block norms:

    ```text
    ||V(g)V(k) - c(g,k)V(gk)|| = max_j ||U(h_(sigma_k j)(g)) U(h_j(k)) - c(.,.) U(h_(sigma_k j)(g) h_j(k))||.
    ```

  - Conclusion. For each fixed `(g,k)` this is a maximum over `r` fixed pairs in `Gamma'`. So if `U_n` is a model
    for `(Gamma', b|Gamma')` at `theta`, then `V_n` is a model for `(Gamma, b)` at `theta`. Hence
    `P(Gamma', b|Gamma') <= P_op`, and (V1) follows.

**(V2) Division rule.** Suppose `[b|Gamma'] = n[beta] + tau` with `tau` torsion. By (V0),
`theta in P(Gamma', b|Gamma')` iff `theta in P(Gamma', n beta)`. Since `c^(n beta)_theta = c^beta_(n theta)`, this
holds iff `n theta in P(Gamma', beta)`. Combining with (V1) gives `P_op = {theta : n theta in P(Gamma', beta)}`.
If `n != 0`, then `x -> n x` is surjective on `R/Z`, so `P(Gamma', beta) = n P_op`.

**(V3) Divisibility index.** Put `E_q = E_infinity / qZ`. Its restriction `E_q|Gamma'` is the preimage of `Gamma'`,
a finite-index subgroup of `E_q`, and it is the central extension of `Gamma'` by `Z/q` with class
`[b|Gamma'] mod q`.

*Index two is attained.*
- `E_2`, the metaplectic double cover, is residually finite by `metaplectic-half-class-has-an-exact-finite-model`,
  which states "The metaplectic double cover `E_2` of `Sp_4(Z)` is residually finite, and some finite quotient
  detects its central involution". The same follows from the displayed equality `(DR2)` of
  `deligne-covers-of-sp2g-z-have-finite-residual-2z` at `n = 4`, because `G/Res_fin(G)` is always residually finite.
  Only the first source is used.
- Pick a finite-index normal `N` of `E_2` with `z_2 notin N`. Then `N` meets the centre `C_2` trivially and maps
  isomorphically onto a finite-index `Gamma' <= Gamma`. So `E_2|Gamma'` splits, and `[b|Gamma'] = 0` in
  `H^2(Gamma';Z/2)`.
- The Bockstein sequence `H^2(Gamma';Z) --2--> H^2(Gamma';Z) --> H^2(Gamma';Z/2)` of `0 -> Z -2-> Z -> Z/2 -> 0`
  is exact. So `[b|Gamma'] = 2[beta]` for some integral class `beta`.

*No other divisibility.* Suppose `[b|Gamma'] = n[beta] + tau` with `tau` torsion and `n` not in `{1,-1,2,-2}`.
- *Choice of `q`.* If `n = 0`, take `q = 3`. If `n` has an odd prime factor `p`, take `q = p`. Otherwise
  `n = +-2^a` with `a >= 2`, and we take `q = 4`. In every case `q | n` and `q >= 3`, so `[b|Gamma'] = tau` in
  `H^2(Gamma';Z/q)`.
- *`tau` comes from a finite cyclic quotient.* The sequence `0 -> Z -> Q -> Q/Z -> 0` gives the exact sequence
  `H^1(Gamma';Q/Z) --d--> H^2(Gamma';Z) --> H^2(Gamma';Q)`. The last group is a `Q`-vector space, so `tau` maps
  to `0` and `tau = d(chi)` for a homomorphism `chi : Gamma' -> Q/Z`. Since `Gamma'` is finitely generated,
  `chi(Gamma') = (1/s)Z/Z` for some `s >= 1`. Write `chi = iota o chibar`, where `chibar : Gamma' -> Z/s` is onto
  and `iota` is the inclusion. Naturality of `d` gives `tau = chibar^*(d iota)`. Hence
  `tau mod q = chibar^*(kappa)` with `kappa in H^2(Z/s; Z/q)`.
- *`E_q|Gamma'` is a fibre product.* Let `1 -> Z/q -> F --pi--> Z/s -> 1` be the extension classified by `kappa`.
  `F` is finite of order `qs`. Pulling back along `chibar` gives the extension with class `chibar^* kappa`, namely
  the fibre product `Gamma' x_(Z/s) F = {(gamma, f) : chibar(gamma) = pi(f)}`. Extensions with equal classes are
  isomorphic, so `E_q|Gamma'` is isomorphic to `Gamma' x_(Z/s) F`, a subgroup of `Gamma' x F`. `Gamma'` is
  residually finite (it is linear over `Z`) and `F` is finite, so `E_q|Gamma'` is residually finite.
- *Residual finiteness passes up.* Let `H <= G` have finite index and be residually finite, and let `g != e`.
  - If `g notin H`, then `g` acts nontrivially on `G/H`. The kernel of that action is a finite-index normal
    subgroup avoiding `g`.
  - If `g in H`, pick a finite-index `N <= H` with `g notin N`. Its normal core in `G` is an intersection of
    finitely many conjugates, so it has finite index, and it lies in `N`.

  So `E_q` is residually finite, and `Res_fin(E_q) = 1`.
- *Contradiction.* `deligne-covers-of-sp2g-z-have-finite-residual-2z` (genus `2`, degree `q >= 3`) gives
  `<z_q^2> <= Res_fin(E_q)`, and `z_q^2 != e` since `q >= 3`. This is the inclusion that node says it uses.

This proves (V3). Note that `n = 0` is included, so `[b|Gamma']` is never torsion.

**(V4).** Take `Gamma'` and `beta` with `[b|Gamma'] = 2[beta]` from (V3). By (V2), `P(Gamma', beta) = 2 P_op`.
- The trivial representation is an exact `beta`-model at parameter `0`. So `0 in P(Gamma', beta)`, and by (V2)
  `1/2 in P_op`, since `2 * (1/2) = 0`.
- If `P_op = (1/m)Z/Z` with `m` even, then `2 P_op = (2/m)Z/Z = (1/(m/2))Z/Z`.
- By (V2), `1/3 in P_op` iff `2/3 in P(Gamma', beta)`. Since `P(Gamma', beta)` is a subgroup, this holds iff
  `1/3 in P(Gamma', beta)`.

**(V5).** Let `Q` be a subgroup of `R/Z` with `1/2 in Q`.
- *(a)* If `U, U'` are models at `theta, theta'`, then `U (x) U'` is a model at `theta + theta'`, with defect at
  most the sum of the two defects, and the entrywise conjugate is a model at `-theta`. Direct sums and
  amplifications keep `theta`. `Q` is a subgroup, so it is closed under (a).
- *(b)* Rephasing keeps `theta`, by (V0). Take `alpha in Aut(Gamma)` with `alpha^*[b] = eps[b] + tau`, where
  `eps = +-1` and `tau` is torsion. `U o alpha` is a model for `alpha^* b` at `theta`, so by (V0) it is a model for
  `b` at `eps theta`. `Q` is closed under negation.

  This covers every automorphism once `H^2(Gamma;Q) = Q`, the fact used in step 0 of
  `sp4-quasirep-windings-budget-and-saturation-proof`. Then `H^2(Gamma;Z)/Tors` has rank one, and `alpha^*`
  acts on it by `+-1`. Nothing below depends on this.
- *(c)* Fix `Gamma'` and `[b|Gamma'] = n[beta] + tau`. By (V3), `n in {+-1, +-2}`.
  - Restrictions of `b`-models at `theta in Q` are `beta`-models at `n theta`. Combining them by (a) on `Gamma'`
    stays in `nQ`.
  - Inducing back via (V1) and (V2) yields exactly the `theta'` with `n theta' in nQ`, that is `Q + (1/n)Z/Z`.
    This equals `Q`, since `1/n in (1/2)Z/Z <= Q`.
  - A finite-index subgroup of `Gamma'` has finite index in `Gamma`, so iterating is again an instance of (c).

  Independently of this bookkeeping, (V2) gives `P(Gamma', beta) = n P_op` outright. So no finite-index subgroup
  carries `beta`-models at parameters outside `n P_op`, whatever their construction.
- *Class kill.* Let `Q_0` be the subgroup generated by `1/3` and `1/2`, namely `(1/6)Z/Z`. It is finite, hence
  closed, and closed under (a) to (c). So no chain of these operations starting from a `1/3`-model reaches
  `1/9`, or any parameter outside `(1/6)Z/Z`. Such a chain would be needed to prove the target's arithmetic hole
  without new analytic input.
- *Where it dies.* The only operation that ever enlarges a subgroup is (c) with `n` not dividing an element
  already present. `1/9` would need `n = 3` or `9`, and `1/3` from `0` would need `3 | n`. (V3) forbids both,
  through the degree-`q = 3` case of Deligne's theorem.

**(V6).** Fix a finite presentation `<S | R>` of `Gamma` with `S` symmetric, and a finite `F`. For each `g in F`,
fix a word `w_g` in `S` representing it. Let `W_F` consist of:
- `(e, e)`;
- the pairs `(p_i, s_(i+1))` of partial products needed to evaluate, left to right, each relator in `R` and each
  `w_g`.

Suppose `V` is block-monomial as in the target, with `c_theta`-defect `< sqrt 2` on `W_F`.
- *Permutation parts compose on the window.* Suppose `sigma(g) sigma(k) j != sigma(gk) j` for some `j`. Take
  `v` a unit vector. Then `V(g)V(k)(e_j (x) v)` is a unit vector supported in block `sigma(g)sigma(k) j`, while
  `c(g,k) V(gk)(e_j (x) v)` is a unit vector in the different block `sigma(gk) j`. So their difference has norm
  `sqrt 2`. Hence `sigma(gk) = sigma(g) sigma(k)` on every pair of `W_F`.
- *They define an action.* From `(e,e)` we get `sigma(e)^2 = sigma(e)`, so `sigma(e) = id`. Let `psi` be the
  homomorphism from the free group on `S` with `psi(s) = sigma(s)`. Evaluating a word `s_1 ... s_l` along its
  partial products gives `sigma(image of the word) = psi(word)`. For a relator the image is `e`, so
  `psi(relator) = id`. Thus `psi` factors through an action of `Gamma` on `{1, ..., r}`, and applied to `w_g` it
  gives `sigma(g) = psi(w_g)` for `g in F`.
- *Consequence.* The stabilizers of this action have index at most `r < infinity`. The stabilizers, and `r`,
  may depend on the model. Nothing here says that a sequence of such models with growing `r` factors through
  one fixed finite-index subgroup. That is the loophole recorded in the target.
