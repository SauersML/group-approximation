# Liftable masas of Kazhdan relative commutants: the positive side, part 1 (2026-09-13)

Lane `ex-hs-masa-lift-positive`. Target: `actor-commutant-has-liftable-masa-in-every-model` (LM).
Inputs used: items 1-4 of `hs-block-gap-iff-liftable-masa-of-actor-commutant` (cited as BG1-BG4).

## 0. Summary

- **Theorem 1 (one model).** For a model `sigma` of a Kazhdan group, three conditions are equivalent:
  a liftable masa of `Q = sigma(G)' cap M`; an internal block algebra containing `sigma(G)` whose
  relative commutant is its center; a sequence of finite partitions with vanishing boundary and the
  summed gap (F2) with vanishing slack. Any positive gap constant forces the Kazhdan constant.
- **Theorem 2 (all models).** (LM) for every model of `G` is equivalent to a dimension-uniform
  partition inequality `DEC_kappa`. It is a `Pi^0_3` sentence when `G` has solvable word problem, so
  its truth does not depend on the ultrafilter or on set theory. The per-block one-level HS Kun
  decomposition implies it.
- **Lemma 3 (chains).** Excess is monotone, countable chains of liftable abelian subalgebras have
  liftable upper bounds, and (LM) for one model is equivalent to a countable chain with excess
  tending to 0. Zorn's lemma fails exactly at chains of uncountable cofinality.
- **Part 2** (`hs-masa-lift-positive-part2-2026-09-13.md`): at the Theorem E pair, (H1) for one model
  already normalizes that model, so (LM) has no marginal consequence for `non-hyperlinear-group`.

## 1. Setting

- `G` countable, `S` finite symmetric generating set, `kappa > 0` with
  `max_s ||pi(s) xi - xi|| >= kappa ||xi - P xi||` for every unitary representation.
- A **model** is a homomorphism `sigma : G -> U(M)`, `M = prod_U M_(n_k)`, with lifts `sigma_k(g)`.
  `Q = sigma(G)' cap M`.
- A **partition** `P = {q_A}` of `M_n` is a finite partition of unity by projections, with span `C(P)`
  and block algebra `D(P) = C(P)' cap M_n = direct_sum_A q_A M_n q_A`. `x_A = q_A x q_A`,
  `tau_A = tau / tau(q_A)`.
- **Boundary:** `b_k(P) = max_s sum_A ||[sigma_k(s), q_A]||_2^2`.
- **Gap slack:** for `kappa' > 0`,
  `gamma_k(P, kappa') = sup_x ( kappa'^2 sum_A ||x_A - tau_A(x_A) q_A||_2^2 - sum_s sum_A ||[q_A sigma_k(s) q_A, x_A]||_2^2 )_+`,
  over self-adjoint contractions `x in D(P)`. `gamma_k <= beta` is (F2) with slack `beta`.
- A **liftable abelian subalgebra** is `C = prod_U C(P_k) <= Q`. Its **excess** is
  `exc(C) = sup { ||x - E_C x||_2 : x in C' cap Q, ||x|| <= 1 }`.

## 2. Theorem 1: one model

For a model `sigma` the following are equivalent.

- (a) `Q` has a liftable masa.
- (b) There are partitions `P_k` with `sigma(G) <= D := prod_U D(P_k)` and `sigma(G)' cap D = Z(D)`.
- (c) For every `j >= 1`, `U`-most `k` admit a partition `P` with `b_k(P) <= 2^-j` and
  `gamma_k(P, kappa) <= 2^-j`.
- (c') The same as (c), with some fixed `kappa' > 0` in place of `kappa`.

*Center of a block ultraproduct.* `Z(prod_U D(P_k)) = prod_U C(P_k)`. The Haar average over
`U(D(P_k))` is the expectation onto `C(P_k)`, so `||x_k - E_(C(P_k)) x_k||_2 <= sup_u ||[u, x_k]||_2`.
Choose maximizing `u_k`. If `x` is central, `(u_k)` commutes with `x`, and `x in prod_U C(P_k)`.

*Proof.*
- (a) => (b). Let `C = prod_U C(P_k)` be a masa of `Q` and `D = C' cap M`. By BG2,
  `D = prod_U D(P_k)`, whose center is `C`. `C <= Q` gives `sigma(G) <= D`. Then
  `sigma(G)' cap D = Q cap C' = C = Z(D)`.
- (b) => (a). `C := Z(D) = prod_U C(P_k)` commutes with `D`, which contains `sigma(G)`. So `C <= Q`.
  By BG2, `C' cap M = D`, so `Q cap C' = sigma(G)' cap D = Z(D) = C`.
- (a) => (c). BG1 gives `b_k(P_k) -> 0`. BG3, with constant `kappa_S = kappa`, gives
  `gamma_k(P_k, kappa) -> 0` along `U`.
- (c) => (c'). Take `kappa' = kappa`.
- (c') => (a). Let `X_j` be the set of `k` admitting a partition at level `j`, so `X_j in U`. Put
  `j(k) = max { j <= k : k in X_1 cap ... cap X_j }`, or `0`, and choose `P_k` witnessing level `j(k)`
  (the trivial partition if `j(k) = 0`). For each `J`, `{k : j(k) >= J}` contains
  `X_1 cap ... cap X_J cap [J, infinity)`, which is in `U`. So `b_k(P_k) -> 0` and
  `gamma_k(P_k, kappa') -> 0` along `U`. BG1 and BG4 make `prod_U C(P_k)` a masa of `Q`. ∎

**Reading.** (b) says that `sigma` is an internal direct sum of "irreducible" blocks: the relative
commutant of the image inside the block algebra is only the block scalars. The gap constant costs
nothing. If partitions with some positive constant exist, then partitions with the Kazhdan constant
exist.

## 3. Theorem 2: all models

`DEC_(kappa')(G, S)`: for every `beta > 0` there are `eps > 0` and `R` such that for every `n` and
every map `u : B_R -> U(n)` with `u_1 = 1` and `||u_g u_h - u_(gh)||_2 <= eps` on `B_R`, there is a
partition `P` of `M_n` with `b(P) <= beta` and `gamma(P, kappa') <= beta`. Here `b` and `gamma` are
computed with `u_s` for `s in S`.

The following are equivalent:
- (i) (LM) for every model of `G`: every sequence `n_k` and every free ultrafilter;
- (ii) `DEC_kappa(G, S)`;
- (iii) `DEC_(kappa')(G, S)` for some `kappa' > 0`.

Moreover, (iv) the one-level decomposition `hs-one-level-expander-block-decomposition` for `G`
implies (i).

*Proof.*
- (ii) => (iii). Trivial.
- (iii) => (i). Let `sigma` be a model with lifts `sigma_k`. Fix `(eps, R)`. Since `sigma` is a
  homomorphism and `B_R` is finite, `sigma_k` restricted to `B_R` is an `(eps, R)`-model for `U`-most
  `k`. So for each `j`, `U`-most `k` admit a partition at level `j`. This is (c') of Theorem 1.
- (i) => (ii). Suppose `DEC_kappa` fails at some `beta`. For each `k`, choose `n_k` and a
  `(1/k, k)`-model `u^(k)` admitting no partition with `b <= beta` and `gamma(., kappa) <= beta`.
  Extend `u^(k)` by `1` outside `B_k`. Then `sigma(g) = [(u^(k)_g)_k]` is a homomorphism into
  `U(prod_U M_(n_k))` for any free `U`. By (i) and Theorem 1 (a) => (c), `U`-most `k` admit such a
  partition. Contradiction.
- (iv) => (i). Let `sigma` be a model. For `U`-most `k`, the lift `sigma_k` is a `delta`-almost
  representation, so it has blocks `p_1, ..., p_m` with `q_0 = 1 - p` of trace at most `eps(delta)`.
  - Adjoin `q_0` as a block. Its boundary is at most `2 tau(q_0)`, so `b_k <= 3 eps(delta)`.
  - For block-diagonal `x`, weight the per-block inequality on each `p_i` by `tau(p_i)` and sum. The
    block `q_0` adds at most `kappa'^2 tau(q_0)` to the right side, so `gamma_k(P, kappa') <= kappa'^2 eps(delta)`.
  - Letting `delta -> 0` gives (c') of Theorem 1. ∎

**Arithmetic form.** Suppose `G` has solvable word problem and `beta, eps` are rational. Then for
fixed `R` and `n`, the inner statement "every `(eps, R)`-model in `U(n)` admits a partition with
`b <= beta` and `gamma <= beta`" is a first-order sentence over the reals:
- a partition has at most `n` members;
- `gamma <= beta` quantifies over contractions.

By Tarski--Seidenberg it is decidable. So `DEC_kappa` is `Pi^0_3`
(`forall beta exists eps, R forall n`), and (i) is absolute: it cannot depend on the ultrafilter, CH,
or forcing.

**Model tests.**
- *Genuine representations satisfy it.* Split into irreducible summands. The boundary is 0, and (T)
  gives the scalar adjoint gap on each summand, since its commutant there is scalar. So `gamma = 0`.
- *The trivial model satisfies it.* Take rank-one blocks. Block-diagonal elements are then diagonal
  and block-scalar, so `gamma = 0`.
- *Not automatic (sketch, not a claim).* For `F_2` at the clock–shift pair on `C^n`, every one-block
  partition has `gamma >= c kappa'^2`, witnessed by slowly varying functions of the clock. Finer
  partitions pay boundary. No model of a Kazhdan group violating `DEC` is known. The candidate
  shape is the uniform cascade of `research/artifacts/hs-coarse-gap-aspect-scales-2026-09-12.md`,
  Section 3.

**Coordinate capture implies it.** Suppose `Q = prod_U A_k` for exact commutants `A_k` of lifts
(Alekseev--Thom Open Problem 6.2 for `sigma`). Choose a maximal family of minimal projections in each
`A_k`. By the capture paragraph of `hs-one-level-expander-block-decomposition`, the partition
algebras form a masa of `prod_U A_k = Q`. So OP 6.2 for `sigma` gives (LM) for `sigma`.

## 4. Lemma 3: chains and excess

1. **Monotone.** If `C <= D` are liftable abelian subalgebras of `Q`, then `exc(D) <= exc(C)`:
   `D' cap Q <= C' cap Q`, and `||x - E_D x||_2 <= ||x - E_C x||_2`. Also `exc(C) = 0` iff `C` is a masa of `Q`.
2. **Countable chains.** Let `C_1 <= C_2 <= ...` be liftable abelian, `C_j = prod_U C(P_(j,k))`, all
   in `Q`. Put `e_(j,k) = sup { ||x - E_(C(P_(j+1,k))) x||_2 : x in C(P_(j,k)), ||x|| <= 1 }`.
   - Choosing maximizers, `C_j <= C_(j+1)` gives `lim_U e_(j,k) = 0`. BG1 gives `lim_U b_k(P_(j,k)) = 0`.
   - `X_J = { k : e_(j,k) <= 2^-J and b_k(P_(j,k)) <= 2^-J for all j <= J }` is in `U`, and the
     `X_J` decrease.
   - Put `J(k) = max { J <= k : k in X_J }` and `D_k = C(P_(J(k),k))`. Then `J(k) -> infinity` along `U`.
   - For `x in C(P_(j,k))` with `j <= J(k)`, iterate `y_(i+1) = E_(C(P_(i+1,k))) y_i` from `y_j = x`.
     This gives `y_(J(k)) in D_k` with `||x - y_(J(k))||_2 <= J(k) 2^-J(k)`.
   - So every `C_j <= D := prod_U D_k`. Since `b_k(D_k) <= 2^-J(k)`, BG1 gives `D <= Q`.
3. **Reduction.** (LM) holds for `sigma` iff there is a countable increasing chain of liftable
   abelian subalgebras of `Q` with `exc(C_j) -> 0`. For (<=), the upper bound `D` of item 2 has
   excess `0` by item 1.
4. **Refinement.** If a liftable `C` is not a masa, it has a strictly larger liftable extension.
   - Take a self-adjoint contraction `y in C' cap Q` outside `C`, lifted blockwise by BG2.
   - *Coarea identity.* For a unitary `u` and `e_theta = 1_((theta, infinity))(y)`,
     `integral ||[u, e_theta]||_2^2 d theta = tau-weighted sum |<xi_i, eta_j>|^2 |lambda_i - mu_j| <= ||[u, y]||_2`,
     by Cauchy--Schwarz in the eigenbases of `y` and `u y u^*`.
   - A grid of mesh `w_k` with random offset costs expected boundary `4 ||[u, y_k]||_2 / w_k`.
     Commuting refinement at most doubles the boundary sum.
   - Choose `w_k -> 0` slowly. The refined partitions have vanishing boundary and resolve `y`.

   The obstruction to Zorn's lemma is therefore exactly a chain of uncountable cofinality. Liftable
   algebras are never separable, so there is no Löwenheim--Skolem shortcut.
