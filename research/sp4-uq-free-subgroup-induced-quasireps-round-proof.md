---
rg: 2
id: sp4-uq-free-subgroup-induced-quasireps-round-proof
kind: route
title: Force the permutation part to be honest, transport blocks along a transversal to get an induced quasi-representation, kill the inducing cocycle by property (T), and bound free patterns by Stuck-Zimmer
target: sp4-uq-free-subgroup-induced-quasireps-round
requires: []
---

Notation as in the target. All norms are operator norms.

**Lemma 0 (norms of block-monomial differences).** Let `A` and `B` be block-monomial with the same permutation `p`.
Then `||A - B|| = max_x ||(A - B)|_{V_x}||`, because `A - B` maps the orthogonal summands `V_x` into the orthogonal
summands `V_{p(x)}`, injectively in `x`.

**Item 1.**
- *Permutations compose where the defect is small.* Let `g, h in W`, and suppose `p_{gh}(x) != p_g p_h(x)`. Take a
  unit vector `v in V_x`. Then `pi(g)pi(h)v` and `pi(gh)v` are unit vectors in the orthogonal spaces
  `V_{p_g p_h x}` and `V_{p_{gh} x}`. Their difference has norm `sqrt 2 > eps`, a contradiction. So
  `p_{gh} = p_g p_h` for `g, h in W`, and `p_e = id` because `pi` is unital.
- *The generators define an action.* Take `S` symmetric. For a word `s_1 ... s_m` with `m <= R`, every prefix lies in
  `B_R`, which is contained in `W`. Induction on `m` gives `p_{s_1...s_m} = p_{s_1} ... p_{s_m}`. Applied to each
  relator, this gives `p_{s_1} ... p_{s_m} = p_e = id`. So `s -> p_s` factors through `Gamma` and is an honest action.
- *Agreement on the ball.* By the same induction, `p_g` equals this action for every `g in B_R`.

**Item 2.**
- *Set-up.* Put `x_0 = e Lambda`, and choose `t_x in Gamma` with `t_x x_0 = x` and `t_{x_0} = e`. Put
  `A(g,x) = pi(g)|_{V_x} : V_x -> V_{gx}`. Restricting the defect bound to `V_x` gives
  `||A(gh,x) - A(g,hx) A(h,x)|| <= eps`.
- *`sigma` is a quasi-representation.* Since `mu x_0 = x_0`, we get `sigma(lambda mu) ~_eps sigma(lambda) sigma(mu)`.
  Also `sigma(e) = 1`.
- *Transport the blocks.* Put `V = V_{x_0}` and `u_x = A(t_x, x_0) : V -> V_x`, and let `U = sum_x u_x`. Write
  `lambda = t_{gx}^{-1} g t_x in Lambda`. Then:
  - `A(g,x) u_x ~_eps A(g t_x, x_0) = A(t_{gx} lambda, x_0)`;
  - `A(t_{gx} lambda, x_0) ~_eps A(t_{gx}, x_0) sigma(lambda) = u_{gx} sigma(lambda)`;
  - so `||u_{gx}^* A(g,x) u_x - sigma(lambda)|| <= 2 eps`.
- *Compare with the induced map.* `Ind_Lambda^Gamma sigma`, on `l^2(X, V)`, has the block `sigma(t_{gx}^{-1} g t_x)`
  from `x` to `gx`. `U^* pi(g) U` has the same permutation. Lemma 0 gives the `2 eps` bound.
- *The rounding consequence.* Let `rho` be a homomorphism of `Lambda` that is `delta'`-close to `sigma` on the
  elements `t_{yx}^{-1} y t_x`. Then `Ind rho` is an honest representation. By Lemma 0,
  `||pi(y) - U Ind(rho)(y) U^*|| <= 2 eps + delta'`.

**Item 3.**
- *Defect.* The block of `pi(g)pi(h)` from `y = (gh)^{-1} x` to `x` is `sigma(c(g, hy)) sigma(c(h, y))`. The block of
  `pi(gh)` is `sigma(c(gh, y)) = sigma(c(g, hy) c(h, y))`. By Lemma 0 the defect is `<= eps`.
- *The class is trivial.* Work on one orbit `Gamma/Lambda`. The cocycle identity makes `phi(lambda) = c(lambda, x_0)`
  a homomorphism `Lambda -> L`.
  - `Lambda` has finite index in `Sp_4(Z)`, so it has property (T) (Kazhdan; `Sp_4(R)` has real rank 2).
  - So `phi(Lambda)` is a finitely generated group with (T).
  - If `L` is free, `phi(Lambda)` is free, and a nontrivial free group maps onto `Z`. So `phi` is trivial.
  - If `L` is torsion-free and Haagerup, `phi(Lambda)` is Haagerup and (T), hence finite, hence trivial.
- *So `c` is a coboundary.* Then `s(x) = c(t_x, x_0)` is well defined, because `c(t lambda, x_0) = c(t, x_0)`.
  Moreover `c(g, x) = c(g t_x, x_0) c(t_x, x_0)^{-1} = s(gx) s(x)^{-1}`.
- *Rounding.* From `||sigma(a b^{-1}) sigma(b) - sigma(a)|| <= eps` we get
  `sigma(a b^{-1}) ~_eps sigma(a) sigma(b)^*`. So the block of `pi(g)` from `g^{-1}x` to `x` is `eps`-close to
  `sigma(s(x)) sigma(s(g^{-1}x))^*`. That is the block of `D (P_g (x) 1) D^*`, where `D = diag(sigma(s(x)))` and
  `(P_g f)(x) = f(g^{-1} x)`. This is an honest representation, and Lemma 0 gives `||pi(g) - D (P_g (x) 1) D^*|| <= eps`
  for every `g`.
- *Ultraproduct.* Pad with an identity block up to dimension `n!`. Padding keeps both the defect and the honesty.
  The classes `Pi = [pi_n]` and `Rho = [rho_n]` then satisfy `||Pi(g) - Rho(g)|| <= eps` in `Q`. Here
  `eps <= eps_0 < 1/(6g-1) < 1/(4g)`, so (UQ) holds for such `Pi`.

**Item 4.**
- *The limit measure.* Let `mu_n` be the push-forward of the uniform measure on `X_n` under `x -> Stab(x)`. It is an
  invariant random subgroup (IRS) of `Gamma`, i.e. a conjugation-invariant measure on the compact space `Sub(Gamma)`.
  Its weak-* limit `mu = lim_omega mu_n` is again an IRS.
- *Its support is countable.* Abért–Glasner–Virág realize each ergodic IRS as the stabilizer IRS of an ergodic
  probability-measure-preserving action. Stuck–Zimmer (Ann. Math. 1994) apply to lattices in higher-rank simple
  groups with (T), which covers `Sp_4(Z) < Sp_4(R)`. They give, for each ergodic component, either a finite atomic
  space, in which case the IRS is uniform on the conjugacy class of one finite-index subgroup, or stabilizers that are
  central almost everywhere, i.e. contained in `{+-1}`. So `mu` is supported on the countable set of finite-index
  subgroups together with the two central subgroups.
- *Conclude.* `H` is neither of finite index nor central, so `mu({H}) = 0`. The sets
  `P_R(H) = {K : K cap B_R = H cap B_R}` are clopen and decrease to `{H}`. Therefore
  `mu_n(P_R(H)) -> mu(P_R(H))` along `omega`, and `mu(P_R(H)) -> 0` as `R -> infinity`.
- *Use.* The projection onto the points of `P_R(H)`, tensored with the blocks, has trace `mu(P_R(H))`. That tends to
  `0` as `R -> infinity`. The trace-preserving quotient `theta : Q -> prod^omega (M_(n!), tr)` is admissible in (UQ)
  and kills trace-zero projections. So a model that imitates `Gamma/H` at every radius has image zero there. This
  use is a remark: item 4 itself is only the density statement.

**Where the method stops.** Items 2 and 3 use defect control on the whole transversal. For windowed models they
reduce rounding to deforming an `eps`-almost-flat unitary local system on a finite cover of a presentation complex to
a flat one on the letter edges. That is not done here.
