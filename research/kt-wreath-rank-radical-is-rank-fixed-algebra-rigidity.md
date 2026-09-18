---
rg: 2
id: kt-wreath-rank-radical-is-rank-fixed-algebra-rigidity
kind: claim
title: The k-linear-sofic radical of the Kun--Thom wreath is the fibre-even kernel iff rank-sofic actions of G have G-invariant Gamma-fixed algebra, and W is k-linear sofic iff the generalized Bernoulli action is k-rank-sofic
distinct_from:
  coset-lamp-seed-radical-is-ce-fixed-algebra-rigidity: that is the Hilbert--Schmidt row, with Connes-embeddable crossed products and the dual shift through a trace; this is the rank row over any field of characteristic not two, where no trace exists and the lamp measure is read off the rank function on commuting idempotents, with rank-realized actions as the new class.
  kt-free-action-hyperlinear-iff-wreath-hyperlinear: that equates hyperlinearity of one free action with hyperlinearity of the wreath; this equates k-linear soficity of the wreath with k-rank-soficity of the generalized Bernoulli action, and computes the rank radical of the wreath through all rank-realized actions.
  kun-thom-wreath-sofic-radical-is-fibre-parity-kernel: that computes the sofic radical, Rad_sof(W) = K_even, from the Hamming defect criterion; this proves that the rank radical equals K_even exactly when the rank row of Kun--Thom Theorem C holds, and that otherwise an explicit lamp quotient of W is k-linear sofic and not sofic.
  c-linear-sofic-group-carries-nontrivial-rigid-defect: that asks for any complex-linear sofic group with a nontrivial rigid defect, equivalently a failure of normalization of the full noncommutative relative commutant; this isolates the commutative (Boolean, measured) special case and proves it is equivalent to the lamp-quotient question for the coset wreath.
  rigid-compression-defect-normalization-dichotomy: that equates defect killing in a class with normalization of relative commutants in its ultraproduct; this replaces the relative commutant by a commuting G-equivariant family of idempotents, on which the rank function is a G-invariant probability measure.
  kun-thom-wreath-linear-sofic: that asks for a rank model of W itself; this proves that such a model exists iff the generalized Bernoulli action of G is k-rank-sofic, the exact rank analogue of the Hayes--Sale permanence that the attempts there found missing.
  profinite-action-fixed-algebra-invariant: that proves fixed-algebra invariance for profinite actions; this makes fixed-algebra invariance for all rank-realized actions the exact rank-row obstruction statement, with profinite and sofic actions as calibrated special cases.
---

**ESTABLISHED** by route `kt-wreath-rank-radical-fixed-algebra-proof`.

## Setting

- `k` is a field with `char k != 2`.
- `R_omega = prod_omega M_(n_i)(k) / {rank-null}` is a rank ultraproduct with rank
  function `rk`, and `U(R_omega)` is its unit group.
- A countable group is `k`-linear sofic iff it embeds in some `U(R_omega)`
  (Arzhantseva--Paunescu, with amplification).
- `Gamma <= G` are countable, `X = G/Gamma` with base point `o = Gamma`, and
  `W = (directSum_X Z/2) x| G` has lamps `e_x`.
- For `a in G`, the seed is `m_a = e_o + e_(ao)`.
- `Rad_(rk,k)(H)` is the intersection of the kernels of all homomorphisms from `H` to
  `k`-linear sofic groups.

**Definition (rank-realized action).** A `k`-rank realization of a p.m.p. Borel action
`G ↷ (Y, nu)` consists of:

- a homomorphism `sigma : G -> U(R_omega)`;
- a Boolean homomorphism `E : MALG(Y, nu) -> Idem(R_omega)`, with commuting image, such that
  `rk E(A) = nu(A)` and `sigma(g) E(A) sigma(g)^(-1) = E(gA)`.

The action is `k`-rank-sofic if it has one.

**Definition (lamp measure).** A homomorphism `theta : W -> U(R_omega)` has a lamp
measure. This is the unique Borel probability measure `mu_theta` on `2^X` whose
cylinders have `mu_theta(C) = rk E_theta(C)`, where `E_theta(C)` is the sum of the joint
eigen-idempotents of the involutions `theta(e_x)` over the patterns in `C`.

`M_k` is the set of lamp measures. Put `odd_S = {omega : sum_(x in S) omega_x odd}`.

## Theorem

1. **(Models give actions.)**
   - Every `mu_theta` is `G`-invariant, and `(theta|_G, E_theta)` extends to a `k`-rank
     realization of `G ↷ (2^X, mu_theta)`.
   - For a lamp configuration `f` with support `S`, `rk(theta(f) - 1) = mu_theta(odd_S)`.
2. **(Actions give models.)** Let `G ↷ (Y, nu)` be `k`-rank-realized, and let
   `pi : Y -> 2^X` be `G`-equivariant. Then `pi_* nu in M_k`. The model is
   `theta(f, g) = prod_(x in supp f) (1 - 2E(pi^(-1){omega_x = 1})) sigma(g)`.
3. **(Seed test.)** `m_a notin Rad_(rk,k)(W)` iff some `k`-rank-realized action of `G`
   has a Borel `Gamma`-invariant set `B` with `nu(aB triangle B) > 0`.
4. **(Radical formula.)** If `G` is `k`-linear sofic, then

   ```text
   Rad_(rk,k)(W) = { f : mu(odd_(supp f)) = 0 for every mu in M_k }.
   ```

5. **(Bernoulli normal form.)** `M_k` contains `delta_0`. It is closed under averaging with
   `delta_0`, under XOR convolution (tensor products of models) and under weak-* limits.
   Hence, if `G` is `k`-linear sofic, the following are equivalent:
   - `W` is `k`-linear sofic;
   - the fair Bernoulli measure on `2^X` lies in `M_k`;
   - the generalized Bernoulli action `G ↷ ({0,1}, fair)^(G/Gamma)` is `k`-rank-sofic.
6. **(Kun--Thom Theorem E pair.)** Let `R_+ = F_q[x_1,...,x_d]`, `R = F_q[x_1^(±1),...,x_d^(±1)]`,
   `r, d >= 3`, `Gamma = EL_r(R_+) < G = EL_r(R) x| SL_d(Z)` and `N = EL_r(R) = <<Gamma>>_G`, and let `K_even` be the fibre-even configurations over
   `G/N`. Then the following are equivalent:
   - **(i)** `Rad_(rk,k)(W) = K_even`;
   - **(ii) (rank Theorem C, `RC_k`)** every `k`-rank-realized p.m.p. action of `G` has
     `L^inf(Y)^Gamma = L^inf(Y)^N`, equivalently a `G`-invariant `Gamma`-fixed algebra;
   - **(iii)** no `k`-linear sofic lamp quotient `W/U` (`U` a `G`-invariant subgroup of the
     lamp group) has a nontrivial seed defect, that is, `[g z g^(-1), gamma] != 1` with
     `z` the image of `e_o`, `g in G` and `gamma in Gamma`.

   If `RC_k` fails, then:
   - there are an action and a set `B` as in (3), with `a in N`;
   - `W/N_mu`, with `mu = pi_* nu` and `N_mu = {f : mu(odd_(supp f)) = 0}`, is `k`-linear
     sofic, contains `G`, and has a nontrivial rigid defect;
   - so `W/N_mu` is not sofic, by `sofic-groups-kill-rigid-compression-defects`.

## Consequences for Question 8.5

- Over `k = C`, a `C`-linear sofic lamp quotient of `W` with a nontrivial seed defect
  exists exactly when a `C`-rank-realized action of `G` moves a `Gamma`-invariant set
  by an element of `N`. Such a quotient is nonsofic, so it answers Q8.5.
  This is `kt-pair-c-rank-sofic-action-moves-fixed-algebra`.
- `W` itself is `C`-linear sofic iff the generalized Bernoulli action, which is nonsofic
  by Kun--Thom Corollary D, is `C`-rank-sofic.
- The rank row is now a statement about a new class of p.m.p. actions. The class lies
  between sofic actions and all actions:
  - sofic actions are rank-realized by permutation matrices and diagonal idempotents;
  - there, `RC_k` is Kun--Thom Theorem C;
  - profinite actions satisfy `RC_k` by `profinite-action-fixed-algebra-invariant`.
- `RC_k` is implied by `DD(k)`, the rank row of the defect criterion, but it constrains
  only commuting idempotent families, so it is the easier obstruction target.
