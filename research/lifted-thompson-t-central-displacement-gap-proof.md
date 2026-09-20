---
rg: 2
id: lifted-thompson-t-central-displacement-gap-proof
kind: route
title: Zassenhaus commutator estimate, diagonal limit to a nontrivial representation of T, and the conjugate tensor square
target: lifted-thompson-t-central-displacement-gap
requires:
  - lifted-thompson-t-perfect-centre-cubically-elliptic
  - lifted-thompson-t-mf-radical-dichotomy
  - lifted-thompson-t-twist-set-is-trivial-or-the-circle
  - central-eigencorners-die-over-full-radical-quotients
  - universal-mf-quotient
---

Conventions are those of `lifted-thompson-t-twist-set-is-trivial-or-the-circle-proof`.

- A corona representation `rho` is the same thing as a sequence of unitary
  maps `U_n : T̄ -> U(k_n)` with `||U_n(gh) - U_n(g) U_n(h)|| -> 0`.
- For `x = [X_n]` in `Q` we have `||x|| = limsup_n ||X_n||`.
- The spectrum of a unitary `[U_n]` is given by (Sp) of that proof.
- The *corner device* is Steps 1a–1b of
  `central-eigencorners-die-over-full-radical-quotients-proof`. For a nonzero
  projection `P` in `rho(T̄)' ∩ Q`, the map `rho_P(g) = rho(g) P` is a corona
  representation into a norm matrix corona `Q_P`, and `Q_P ≅ PQP` isometrically
  with unit `P`. In particular the displacement of `rho_P` is
  `||(rho(z) - 1) P||`, and `sp(rho_P(z))` is the spectrum `X_P` of
  `rho(z) P` in `PQP`.
- `T̄ / <z> = T`: the kernel of the projection `T̄ -> T` is the centre `<z>`
  (see `lifted-thompson-t-perfect-centre-cubically-elliptic`).

Facts used from the requirements.

- **(F1)** `T̄` is perfect and finitely presented: item 2 of
  `lifted-thompson-t-perfect-centre-cubically-elliptic` and item 4 of
  `lifted-thompson-t-mf-radical-dichotomy`.
- **(F2)** `T` is simple, so `Rad_MF(T) ∈ {1, T}`. By `universal-mf-quotient`,
  "`T` not full" is equivalent to "`T` MF". "`T` full" means that every corona
  representation of `T` is trivial (definition of `Rad_MF` in
  `universal-mf-quotient`).
- **(F3)** `Rad_MF(T̄) ∈ {1, T̄}` (item 1 of
  `lifted-thompson-t-mf-radical-dichotomy`).
- **(F4)** `Sigma = {1}` if `T` is full and `Sigma = S^1` if `T` is MF (item 2
  of `lifted-thompson-t-twist-set-is-trivial-or-the-circle`).
- **(F5)** Tensor products and entrywise conjugates of corona representations
  are corona representations. Restricting to an infinite set of indices gives
  a corona representation. See item 1 of the twist-set proof.

## Item 0: the Zassenhaus gap

By (F1), `T̄` is finitely generated and perfect. So each generator `s_i` can be
written as a product `s_i = prod_(j <= p) [a_ij, b_ij]` of `p` commutators, where
every `a_ij` and `b_ij` is a word of length at most `l` in the `s_k^(±1)`. Put
`delta = 1 / (2 p l^2)`.

Let `sigma : T̄ -> U(D)` be a homomorphism and put `eps = max_i ||sigma(s_i) - 1||`.
Three estimates hold for unitaries `A` and `B`.

- `||AB - 1|| <= ||A - 1|| + ||B - 1||` and `||A^(-1) - 1|| = ||A - 1||`. So
  every word `w` of length at most `l` satisfies `||sigma(w) - 1|| <= l eps`.
- `||A B A^(-1) B^(-1) - 1|| = ||AB - BA||`, and
  `AB - BA = (A - 1)(B - 1) - (B - 1)(A - 1)`. So
  `||[A, B] - 1|| <= 2 ||A - 1|| ||B - 1||`.
- Combining these, `||sigma(s_i) - 1|| <= sum_j 2 (l eps)^2 = 2 p l^2 eps^2`.

Taking the maximum over `i` gives `eps <= 2 p l^2 eps^2`. So either `eps = 0`
or `eps >= delta`. Nothing about `D` was used beyond its being a unital
C\*-algebra. When `eps = 0`, `sigma` is trivial because the `s_i` generate.

## Item 1: N is closed

Enumerate `T̄ = {g_1, g_2, ...}`. Let `rho_j` have displacements `c_j -> c`,
with lifts `U^(j)_n`. We have `c_j = limsup_n ||U^(j)_n(z) - 1||`, and almost
multiplicativity holds for all large `n`. So we can choose `n_j` such that:

- `||U^(j)_(n_j)(g_a g_b) - U^(j)_(n_j)(g_a) U^(j)_(n_j)(g_b)|| < 1/j` for all
  `a, b <= j`;
- `| ||U^(j)_(n_j)(z) - 1|| - c_j | < 1/j`.

The diagonal sequence `W_j = U^(j)_(n_j)` is a corona representation, and its
displacement is `lim_j ||W_j(z) - 1|| = c`. So `c ∈ N`.

## Item 2: T full iff 0 is isolated in N

**(⇒)** Let `T` be full, and suppose there are `rho_j` with displacements
`0 < c_j -> 0`. Each `rho_j` is nontrivial. By item 0 applied in `D = Q_j`,
`max_i ||rho_j(s_i) - 1|| >= delta`. So some `i` satisfies
`limsup_n ||U^(j)_n(s_i) - 1|| >= delta`. Choose `n_j` such that:

- the multiplicativity condition of item 1 holds;
- `||U^(j)_(n_j)(z) - 1|| < c_j + 1/j` (true for all large `n`);
- `max_i ||U^(j)_(n_j)(s_i) - 1|| > delta - 1/j` (true for infinitely many `n`).

The diagonal corona representation `sigma = [W_j]` has `||sigma(z) - 1|| = 0`,
because `c_j -> 0`. It also has `max_i ||sigma(s_i) - 1|| >= delta`, because the
maximum of finitely many limsups is the limsup of the maximum. So `sigma`
factors through `T̄ / <z> = T` and is a nontrivial corona representation of
`T`. This contradicts (F2). Hence some `eta > 0` has `N ∩ (0, eta) = ∅`.

**Corners.** Let `P` be as in the statement. By the corner device, `rho_P` is a
corona representation of `T̄` with displacement `||(rho(z) - 1) P|| < eta`. So
this displacement is `0`, that is `rho_P(z) = 1`. Then `rho_P` factors through
`T` and is trivial, so `rho(g) P = P` for all `g`.

**(⇐)** Suppose `T` is not full. Then `T` is MF by (F2), and item 3 (⇒) below
gives `N = [0, 2]`, in which `0` is not isolated.

## Item 3: T MF iff N = [0, 2]

**(⇒)** If `T` is MF, then `Sigma = S^1` by (F4). For `mu ∈ S^1`, a witness
`sigma` with `sigma(z) = mu 1` has displacement `|mu - 1|`. As `mu` ranges over
`S^1`, this takes every value in `[0, 2]`.

**(⇐)** If `N = [0, 2]`, then `0` is not isolated. By item 2 (⇒), `T` is not
full, so `T` is MF by (F2).

## The conjugate tensor square

Let `rho = [U_n]` be a corona representation and put
`rho ⊗ rho̅ = [U_n ⊗ Ū_n]`, which is a corona representation by (F5).

- **(T1)** `||(rho ⊗ rho̅)(z) - 1|| <= diam sp(rho(z))`.

  *Proof.* `U_n(z) ⊗ Ū_n(z)` is a normal matrix with spectrum
  `{ x y̅ : x, y ∈ sp U_n(z) }`, and `|x y̅ - 1| = |x - y|`. So its distance
  from `1` is `d_n = diam sp U_n(z)`, and the displacement is
  `limsup_n d_n`. Pick `n_k` with `d_(n_k) -> limsup d_n`, and points
  `x_k, y_k ∈ sp U_(n_k)(z)` with `|x_k - y_k| = d_(n_k)`. Pass to a
  subsequence with `x_k -> x` and `y_k -> y`. Then
  `liminf_n dist(x, sp U_n(z)) = 0`, and likewise for `y`. So `x` and `y`
  lie in `sp(rho(z))` by (Sp), and `|x - y| = limsup d_n`.
- **(T2)** If `(rho ⊗ rho̅)(z) = 1` and `rho(z) != 1`, then `Sigma != {1}`.

  *Proof.* Now `d_n -> 0`. Pick `mu_n ∈ sp U_n(z)`. Then
  `||U_n(z) - mu_n 1|| = max_x |x - mu_n| <= d_n -> 0`, so
  `rho(z) = [mu_n 1]`. Since `rho(z) != 1`, some subsequence has
  `mu_n -> mu != 1`. Restricting `rho` to it (F5) gives `rho'` with
  `rho'(z) = mu 1`.

## Item 4: trichotomy, (Small) and (Arc)

By (F3) and `universal-mf-quotient`, `N != {0}` iff some `rho` moves `z` iff
`Rad_MF(T̄) != T̄` iff `T̄` is MF. Combining with items 2 and 3 and (F2):

- If `T̄` is not MF, then `N = {0}`.
- If `T` is MF, then `N = [0, 2]`.
- Otherwise `T̄` is MF and `T` is full. Then `N != {0}`, and item 2 gives
  `N ⊆ {0} ∪ [eta, 2]`.

The three cases are disjoint, because `{0}` and `[0, 2]` both fail the third
description. The third case is exactly "`T̄` MF and `T` not MF", that is
"(D) fails".

- **(Small) ⟺ (D).** Case 1 satisfies (Small) vacuously and case 2 has
  `inf = 0`. In case 3, `inf (N \ {0}) >= eta`.
- **(D) ⟹ (Arc).** If `T̄` is MF, then `T` is MF by (D), so `Sigma = S^1`
  by (F4). A witness for `mu = e^(i eps / 2)` has `rho(z) = mu 1 != 1` and
  `sp(rho(z)) = {mu}`.
- **(Arc) ⟹ (Small).** Let `N != {0}`, so `T̄` is MF. Given `eps`, take `rho`
  from (Arc); then `diam sp(rho(z)) <= eps`.
  - If `(rho ⊗ rho̅)(z) != 1`, then by (T1) its displacement lies in
    `N ∩ (0, eps]`.
  - Otherwise (T2) gives `Sigma != {1}`, so `T` is MF by (F4) and (F2). Then
    `N = [0, 2]` by item 3.

  In both cases `inf (N \ {0}) <= eps`.

## Item 5: spread when T is full

Let `T` be full, and let `rho` and `P` be as in the statement. By the corner
device, `rho_P` is a corona representation with `sp(rho_P(z)) = X_P`. Suppose
`diam X_P < eta`.

- By (T1) applied to `rho_P`, the displacement of `rho_P ⊗ rho̅_P` is less
  than `eta`. It lies in `N`, so it is `0` by item 2.
- If `rho_P(z) != 1`, then (T2) gives `Sigma != {1}`. This contradicts (F4),
  since `T` is full.
- So `rho_P(z) = 1`, that is `rho(z) P = P` and `X_P = {1}`. The corner clause
  of item 2 then gives `rho(g) P = P` for all `g`.

**Dilated version.** `lambda` is an injective endomorphism of `T̄` with
`lambda^j(z) = t_j` (item 2(c) of the twist-set proof). So `rho o lambda^j` is
a corona representation, with `(rho o lambda^j)(z) = rho(t_j)` and
commutant `rho(lambda^j T̄)' ∩ Q`. Apply the above to it.

## Item 6: homotopy constructions are dead

Let `pi : T̄ -> U(C(Y, D))` be scalar at `y_0`. For each `y`, evaluation
gives a homomorphism `pi_y : T̄ -> U(D)`. The function
`f(y) = max_i ||pi(s_i)(y) - 1||` is continuous.

- By item 0, `f` takes values in `{0} ∪ [delta, 2]`.
- `Y` is connected, so `f` is constant.
- `pi_(y_0)` takes values in the abelian group `S^1 1`. Since `T̄` is perfect
  (F1), it is trivial, so `f(y_0) = 0`.

Hence `f = 0`, so every `pi(s_i) = 1` and `pi` is trivial.

The unitization of `C_0((0,1], D)` is the subalgebra of `C([0,1], D)` of
functions with `f(0) ∈ C 1`. The unitization of `C_0((0,1), D)` is the
subalgebra with `f(0) = f(1) ∈ C 1`. Both are unital subalgebras of
`C([0,1], D)`, so their unitary groups sit in `U(C([0,1], D))` with a
scalar fibre at `0`.

∎

## Remarks

- **What the O_2 counterexample used.** In
  `o2-suspension-central-unitary-evades-commutant-corners`, the corner-free
  central unitary comes from a group `H` inside `U(C)`, where `C` is the
  unitized suspension of `O_2`. By item 6, every homomorphism `T̄ -> U(C)` is
  trivial. So that configuration, a central unitary homotoped through a
  connected family to a scalar fibre, cannot carry `T̄`. This does not revive
  `commutant-projection-extraction` for `T̄`. It only removes that one witness,
  and any suspension-type or cone-type variant of it, as a model of the
  failure world of (D).
- **Where this stops.** In the failure world of (D), every corona
  representation that moves `z` has displacement at least `eta`. Every nonzero
  commutant corner, for `z` and for each `t_j`, has `z`-spectrum of diameter at
  least `eta`, unless `rho` is trivial on it. Proving (D) is now exactly
  producing corona representations of `T̄` whose central translation is moved
  by an arbitrarily small nonzero amount, or whose `z`-spectrum is nontrivial
  but lies in a short arc.
- **Novelty.** Item 0 is the standard commutator estimate behind operator-norm
  local rigidity of perfect groups (compare item (A) of
  `simple-kazhdan-mf-lives-in-gap-near-representations`). What is new here is
  its combination with the diagonal argument into item 2, and with the conjugate
  tensor square into items 4 and 5. Not independently reviewed.

