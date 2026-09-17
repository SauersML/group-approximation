---
rg: 2
id: monomial-qca-topological-absorption-proof
kind: route
title: Read the diagonal part of a monomial automaton as a decoder and its permutation part as a translation lift, then trivialize the lift over the decoder
target: monomial-quantum-automata-are-topological-bernoulli-absorptions
requires: []
---

Notation as in the claim.

- Configurations `u in A^G` with `A = Z/d`. The shift is `(lambda_g u)_h = u_{g^-1 h}`, and on the algebra
  `lambda_g(A_h) = A_{gh}`.
- `A_F = (x)_{h in F} M_d` acts on `l^2(A^F)`, and `delta_e` is the configuration equal to `1` at `e` and `0` elsewhere.
- For a finite-window bijection `pi` of `A^G`, write `U_pi |u> = |pi u>`. For `f in C(A^G)`, `U_pi f U_pi^* = f o pi^-1`.
  Indeed, `U_pi f U_pi^* |pi u> = U_pi f |u> = f(u) |pi u>`.
- The Weyl relations at a site are `X^d = Z^d = 1` and `X Z X^* = zeta^-1 Z`. Operators at different sites commute.

**Standard facts.**

- (S1) **Universality of `M_d`.** Unitaries `x, z` in a unital C*-algebra with `x^d = z^d = 1` and `z x = zeta x z`
  generate a unital image of `M_d`. The universal C*-algebra of these relations is `M_d`, and the representation is
  unique up to multiplicity. Such an image is injective because `M_d` is simple.
  Commuting images of `M_d` give a unital *-homomorphism `A_F -> B`, injective because `A_F` is simple. Compatible
  maps on the `A_F` are isometric and so extend to `A`.
- (S2) **The diagonal is a masa.** `C(A^G)` is a maximal abelian subalgebra of `A`. Let `E_F : A -> A_F` be the
  trace-preserving conditional expectation, and suppose `a` commutes with `C(A^G)`. Then `E_F(a)` commutes with the
  diagonal of `A_F`, so it lies in that diagonal. Since `E_F(a) -> a`, `a in C(A^G)`.
- (S3) **Curtis–Hedlund–Lyndon.** Continuous shift-equivariant maps between subshifts are sliding block codes. The
  inverse of a bijective one is again one.
- (S4) **Monomials.** Monomial unitaries in `A_F` form the group `D_F x| S(A^F)`, where `D_F` is the diagonal unitaries
  and `S(A^F)` the permutations of `A^F`. The factorization `m = D U_pi` is unique. It is unchanged when `F` is
  enlarged, since `m (x) 1 = (D (x) 1) U_{pi x id}`. So "permutation part" is a well-defined homomorphism, and it
  commutes with every automorphism of `A` that preserves the diagonal and the permutation unitaries, such as
  `lambda_g`.

## Step 1. (1) gives (3)

Let `Phi` be monomial diagonal-preserving, with `Phi(A_e) <= A_N` for a finite `N`.

- **Diagonal part.** `Phi(Z_e)` is a diagonal unitary in `A_N` with `Phi(Z_e)^d = 1`. So `Phi(Z_e) = zeta^{s(u|N)}` for
  some `s : A^N -> Z/d`. By equivariance, `Phi(Z_g) = zeta^{sigma(u)_g}` with `sigma(u)_g = s((lambda_g^-1 u)|N)`, and
  `sigma` is a cellular automaton. Both `Phi|C(A^G)` and `sigma^*` are unital *-homomorphisms that agree on the
  generators `Z_g`, so `Phi(f) = f o sigma` for every `f in C(A^G)`.
- **Permutation part.** Write `Phi(X_e) = D_e U_{T_e}` by (S4), with `T_e` a bijection of `A^G` that changes only
  coordinates in `N` and reads only coordinates in `N`. Put `T_g = lambda_g T_e lambda_g^-1`. By (S4) and equivariance,
  this is the permutation part of `Phi(X_g)`, and it changes only coordinates in `gN`.
- **Relations.** Apply the permutation-part homomorphism to `Phi(X_e)^d = 1` and `Phi(X_e) Phi(X_g) = Phi(X_g) Phi(X_e)`.
  This gives `T_e^d = id` and `T_e T_g = T_g T_e`.
- **Translation.** Diagonal unitaries commute with `f`, so
  `Phi(X_e) Phi(Z_g) Phi(X_e)^* = U_{T_e} Phi(Z_g) U_{T_e}^* = Phi(Z_g) o T_e^-1`. The Weyl relation says this equals
  `zeta^{-[g=e]} Phi(Z_g)`. So `sigma(T_e^-1 v)_g = sigma(v)_g - [g = e]` for all `g` and `v`, that is,
  `sigma o T_e = sigma + delta_e`.
- **Strictness.** It is shown in Step 4 that `Phi` strict forces `sigma` non-injective.

## Step 2. The lift generates a continuous action of `(Z/d)^G`

Let `T_g` change only coordinates in `gR` and read only coordinates in `gW`, with `R <= W` finite. For finitely
supported `x`, put `T^x = prod_g T_g^{x_g}`. This is well defined because the `T_g` commute and have order `d`, and it
satisfies `T^{x+y} = T^x T^y` and `sigma(T^x u) = sigma(u) + x`.

- **Stabilization.** Fix `h`, and let `F` be finite with `F >= h R^-1`. For finite `F' >= F`, write
  `T^{x|F'} = T^{x|F' \ F} o T^{x|F}`. The first factor changes only coordinates in `(F' \ F) R`, and this set does not
  contain `h`, because `h in gR` means `g in hR^-1 <= F`. So `(T^{x|F'} u)_h = (T^{x|hR^-1} u)_h`.
- **Definition and locality.** For arbitrary `x in (Z/d)^G`, set `(T^x u)_h = (T^{x|hR^-1} u)_h`. This coordinate
  depends only on `x` on `hR^-1` and on `u` on `hR^-1 W`. So `(x, u) -> T^x u` is continuous.
- **Properties.** It agrees with the finite products on finitely supported `x`. By density and continuity it is an
  action, `T^{x+y} = T^x T^y` and `T^0 = id`, and `sigma(T^x u) = sigma(u) + x` for all `x`. It is equivariant,
  `lambda_g T^x lambda_g^-1 = T^{lambda_g x}`, because `lambda_g T_k lambda_g^-1 = T_{gk}` and
  `lambda_g delta_k = delta_{gk}`.
- **Consequence.** `sigma` is onto, since `sigma(T^x u) = sigma(u) + x` reaches every configuration.

## Step 3. (3) gives (2)

Put `Y = sigma^-1(0)`, a closed shift-invariant subset of `A^G`, hence a subshift. Define
`Psi(u) = (sigma(u), T^{-sigma(u)} u)`.

- **Range.** `sigma(T^{-sigma(u)} u) = sigma(u) - sigma(u) = 0`, so `Psi` maps into `A^G x Y`.
- **Continuity and equivariance.** `Psi` is continuous by Step 2. It is equivariant:
  `Psi(lambda_g u) = (lambda_g sigma(u), T^{-lambda_g sigma(u)} lambda_g u) = (lambda_g sigma(u), lambda_g T^{-sigma(u)} u)`.
- **Inverse.** `Theta(x, y) = T^x y` is continuous. `Psi(Theta(x, y)) = (x + 0, T^-x T^x y) = (x, y)`, and
  `Theta(Psi(u)) = T^{sigma(u)} T^{-sigma(u)} u = u`. So `Psi` is a homeomorphism.
- **Nontriviality.** If `sigma(u) = sigma(u')` with `u != u'`, then `T^{-sigma(u)} u` and `T^{-sigma(u)} u'` are
  distinct points of `Y`. So `|Y| >= 2` exactly when `sigma` is not injective.

## Step 4. Strictness criterion (c)

Let `Phi` be monomial diagonal-preserving with diagonal part `sigma` and lift `T`.

- **`sigma` not injective implies `Phi` strict.**
  - `sigma` is onto (Step 2) and not injective. So there is `f in C(A^G)` separating two points with the same image,
    and `f` is not of the form `k o sigma`. Hence `Phi(C(A^G)) = sigma^* C(A^G)` is a proper subalgebra of `C(A^G)`.
  - Suppose `Phi` were onto. Then `Phi` would be a *-automorphism, by (S1), injectivity from simplicity. So
    `Phi^-1(C(A^G))` would be abelian, contain `C(A^G)`, and contain `Phi^-1(f)`, which is not in `C(A^G)`.
  - That contradicts (S2).
- **`sigma` injective implies `Phi` onto.**
  - `sigma` is a bijective cellular automaton, so by (S3) its inverse is one too, and `sigma^* C(A^G) = C(A^G)`. Thus
    `C(A^G) <= Phi(A)`.
  - For each `u`, put `c(u) = sigma(u + delta_e) - sigma(u)`. It is supported in the finite set of `g` whose window
    `gN` contains `e`, and it depends on `u` only on a finite window `V`.
  - `sigma(T^{c(u)} u) = sigma(u + delta_e)`, so by injectivity `T^{c(u)} u = u + delta_e`. Hence
    `X_e = sum_{w in A^V} U_{T^{c(w)}} P_w`, where `P_w` is the diagonal projection onto configurations with pattern
    `w` on `V`.
  - Each `U_{T^c}` is the product of `Phi(prod_g X_g^{c_g})` with the inverse of a diagonal unitary, so it lies in
    `Phi(A)`. Hence `X_e in Phi(A)`, `Z_e in Phi(A)`, and by equivariance and closedness `Phi(A) = A`.

Together with Step 1 this completes (1) to (3), with `sigma` not injective.

## Step 5. (2) gives (1)

Let `Psi : A^G -> A^G x Y` be an equivariant homeomorphism with `|Y| >= 2`, and put `sigma = pr_1 o Psi`.

- **Windows.** By (S3), `Psi` and `Psi^-1` are sliding block codes, with finite memory sets `M_1` and `M_2`.
  Addition of `(delta_e, 0)` is a homeomorphism of `A^G x Y`.
- **The lift.** Put `T_e(u) = Psi^-1(Psi(u) + (delta_e, 0))`.
  - If `h notin e M_2^-1`, then `Psi^-1(.)_h` does not read coordinate `e` of the first factor, so `(T_e u)_h = u_h`.
    So `T_e` changes only coordinates in the finite set `R = e M_2^-1`.
  - It reads `u` only on `W = R M_2 M_1 union R`.
  - `T_e` is a bijection with inverse `u -> Psi^-1(Psi(u) - (delta_e, 0))`. It fixes coordinates outside `R`, so for
    each exterior pattern on `W \ R` it permutes `A^R`. Thus `T_e` is a permutation of `A^W`, and `U_{T_e} in A_W`.
- **Lift relations.** Since the translations commute and have order `d`, `T_e^d = id` and `T_e T_g = T_g T_e`. By
  equivariance of `Psi`, `lambda_g T_e lambda_g^-1 = T_g`. And `sigma(T_e u) = sigma(u) + delta_e`.
- **The automaton.** Set `Phi(X_g) = U_{T_g}` and `Phi(Z_g) = zeta^{sigma(u)_g}`, a diagonal unitary in a finite
  local algebra. The relations hold:
  - `U_{T_g}^d = 1` and `Phi(Z_g)^d = 1`.
  - The `U_{T_g}` commute with each other, and the `Phi(Z_g)` commute with each other.
  - `U_{T_e} Phi(Z_g) U_{T_e}^* = Phi(Z_g) o T_e^-1 = zeta^{-[g=e]} Phi(Z_g)`.

  So each pair `(Phi(X_g), Phi(Z_g))` satisfies the Weyl relations. Operators attached to different sites commute. By
  (S1), `Phi` extends to a unital *-endomorphism of `A`. It is equivariant, with finite propagation
  `Phi(A_e) <= A_{W union M_1}`.
- **Conclusion.** `Phi` is monomial diagonal-preserving with diagonal part `sigma`. The map `sigma` is not injective,
  since its fibers are `Psi^-1({x} x Y)`, of size `|Y| >= 2`. By Step 4, `Phi` is strict.

## Step 6. Consequences (a) and (b)

- **(a) Strict pair.** Let `u_0` be a constant configuration. `Psi(u_0)` is shift-fixed, so `Psi(u_0) = (x_0, y_0)`
  with `y_0 in Y` shift-fixed.
  - `tau(x) = Psi^-1(x, y_0)` is continuous, equivariant and injective.
  - Its image `Psi^-1(A^G x {y_0})` misses `Psi^-1(A^G x {y_1})` for any `y_1 != y_0` in `Y`, so `tau` is not onto.
  - `sigma o tau = pr_1 o Psi o Psi^-1 (., y_0) = id`.
- **(b) Measure.** Each `T_e` permutes patterns on a finite window, so it preserves the uniform Bernoulli measure `mu`.
  - Then `(+delta_e)_* sigma_* mu = (sigma o T_e)_* mu = sigma_* mu`.
  - So `sigma_* mu` is invariant under the dense subgroup `sum_G Z/d` of the compact group `(Z/d)^G`. The action
    `(Z/d)^G x Prob(A^G) -> Prob(A^G)` is weak*-continuous, so `sigma_* mu` is invariant under all of `(Z/d)^G`, and
    therefore it is the Haar measure `mu`.
  - `Phi|C(A^G) = sigma^*` by construction. So `sigma` satisfies (D1) and (D2).
- **Surjunctive groups.** If `G` is surjunctive on `A^G`, (a) excludes (2), and so by the theorem no strict monomial
  diagonal-preserving automaton exists.

## Step 7. Remarks recorded in the claim

- **Other alphabets.** For a finite abelian group `A` of order `d`, use the Weyl system
  `X_a |b> = |a + b>`, `Z_chi |b> = chi(b) |b>`. Steps 1 to 6 run verbatim with generators `a` of `A` in place of
  `1 in Z/d` and characters in place of powers of `Z`. Condition (2) involves only `|A|`.
- **Clifford automata.** A symplectic `diag(A, B^*)` sends `X`-type Weyl operators to `X`-type ones and `Z`-type ones
  to `Z`-type ones, up to phase. So it is monomial and diagonal-preserving. The resulting `Psi` is additive, which is
  the algebraic absorption of `stable-finiteness-failure-is-algebraic-bernoulli-absorption`.
- **The tree rule.** `alpha(Z_v) = Z_c^h Z_c'^h` gives `sigma(u)_v = h(u_c + u_c')`. The lift `T_v` adds `1` at `c`
  and at `c'`, so `sigma(T_v u)_v = sigma(u)_v + 2h = sigma(u)_v + 1`, and the other coordinates of `sigma` are
  unchanged. Steps 1 to 5 use only the symmetry through `T_g = lambda_g T_e lambda_g^-1`, and there the lift is given
  directly at every vertex.
- **A non-monomial extension.** On the tree, `a = X_c X_c'^-1` and `b = Z_c^h Z_c'^-h` satisfy `ba = zeta^{2h} ab = zeta ab`.
  They commute with `alpha(A)` and generate `M_p`. Take `P = p^-1 sum_k a^k` and `W_v = 1 + (zeta - 1) P`.
  - `W_v^p = 1`, and `W_v` commutes with `alpha(A)` and with `W_{v'}` for `v' != v`, because the child sets are
    disjoint.
  - `W_v` is invariant under swapping `c` and `c'`, which inverts `a`.
  - Each row of `P` has `p` entries equal to `1/p`, because `a` moves `u` along an orbit of length `p`. So `W_v` is
    not monomial.
  - Therefore `alpha'(X_v) = alpha(X_v) W_v`, `alpha'(Z_v) = alpha(Z_v)` is a strict, diagonal-preserving,
    non-monomial automaton with the same `sigma`. Strictness follows from the first half of Step 4, which uses only
    `Phi|C(A^G) = sigma^*` with `sigma` not injective.
