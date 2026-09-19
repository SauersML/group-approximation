---
rg: 2
id: kazhdan-mapping-torus-uniform-conjugacy-gap-proof
kind: route
title: Kazhdan dichotomy in coronas, diagonal selection of approximate conjugacies, and cyclic block shifts
target: kazhdan-mapping-torus-exact-radical-iff-uniform-conjugacy-gap
requires:
  - universal-mf-quotient
  - matricial-stability-identifies-radicals
  - mapping-torus-mf-radical-lies-in-finite-residual
---

Notation is that of the claim: `K`, `(S,kappa)`, `phi`, `G`, `t`, the
coronas `C`, and `d`.  For each `s in S`, fix a word `w_s` in `S^{+-1}`
representing `phi(s)`.  Fix a (possibly infinite) enumeration
`R_K = {r_1, r_2, ...}` of defining relators of `K` on `S`.

## Imported facts

- **(KP) Kazhdan pair.**  If a unitary representation of `K` on a Hilbert
  space has no nonzero invariant vector, then every vector `xi` satisfies
  `max_{s in S} ||pi(s) xi - xi|| >= kappa ||xi||`.  See Bekka--de la
  Harpe--Valette, *Kazhdan's Property (T)*, Definition 1.1.3.
  - A (T) group is finitely generated, and every finite generating set is a
    Kazhdan set (ibid., Theorem 1.3.1 and Proposition 1.3.2).
  - So `S` may be taken finite and generating.
- **(Mal) Malcev.**  A finitely generated subgroup of `GL_k(C)` is residually
  finite.  See A. I. Mal'cev, *On isomorphic matrix representations of
  infinite groups*, Mat. Sb. 8 (1940).
- **(Cor) Coronas.**  Write `C = prod_n M_{k_n} / (+)_n M_{k_n}` and let
  `x = [(x_n)_n]`.
  - (Cor1) `||x|| = limsup_n ||x_n||`.
  - (Cor2) Every unitary of `C` has a lift by a sequence of unitaries.
    - A lift `(x_n)` has `||x_n^* x_n - 1|| -> 0`.
    - So `x_n` is invertible for large `n`, and its polar part is a unitary
      lift; put `1` at the finitely many other `n`.
  - (Cor3) `M_p(C)` is the corona with dimensions `p k_n`.  This is because
    `M_p` commutes with products, with direct sums and with quotients.
- **(Rad) The radical.**  By `universal-mf-quotient`, `Rad_MF(G)` is the
  intersection of the kernels of homomorphisms `G -> U(C)` over all coronas
  `C`.
  - The scalar map `k t^m -> exp(i m) 1` is such a homomorphism and is
    injective on the `Z` factor.
  - So `Rad_MF(G) <= K x {0}` always.
  - Hence (a) holds iff every corona representation of `G` is trivial on `K`.

## Step 0. A presentation of G

Let `Gamma = < S, t | R_K, t s t^-1 = w_s (s in S) >`.

1. Sending `S` to `K x {0}` and `t` to `t` gives a surjection
   `Gamma -> G`.
2. The relators `R_K` give a homomorphism `iota : K -> Gamma`.
3. The homomorphisms `k -> t iota(k) t^-1` and `iota o phi` agree on `S`, so
   they are equal.
4. Applying step 3 to `phi^-1(k)` gives
   `t^-1 iota(k) t = iota(phi^-1(k))`.
5. So `k t^m -> iota(k) t^m` is a well-defined homomorphism `G -> Gamma`.
   It respects `(k t^m)(k' t^m') = k phi^m(k') t^(m+m')`.
6. The two maps are mutually inverse on generators.

So `G = Gamma`.  Consequently, unitaries `X(s)`, `Y` in a unital C*-algebra
define a homomorphism `G -> U` exactly when every `r in R_K` satisfies
`r(X) = 1`, and every `s in S` satisfies `Y X(s) Y^* = w_s(X)`.

## Step 1. Kazhdan dichotomy in a unital C*-algebra

**Lemma KD.**  Let `A` be a unital C*-algebra and `pi : K -> U(A)` a
homomorphism with `max_{s in S} ||pi(s) - 1|| < kappa`.  Then `pi` is
trivial.  Equivalently, a nontrivial `pi` has
`max_s ||pi(s) - 1|| >= kappa`.

*Proof.*
1. Represent `A` faithfully and unitally on a Hilbert space `H`
   (Gelfand--Naimark).  Then `pi` becomes a unitary representation of `K` on
   `H`.
2. Let `H_0` be the closed subspace of `K`-invariant vectors.  Its orthogonal
   complement is `K`-invariant, and the restricted representation has no
   nonzero invariant vector.
3. If `xi` is a unit vector in that complement, then (KP) gives
   `kappa <= max_s ||pi(s) xi - xi|| <= max_s ||pi(s) - 1|| < kappa`, which
   is impossible.
4. So `H = H_0`: each `pi(k)` acts as the identity on `H`, and by
   faithfulness `pi(k) = 1`.  `[]`

**Proof of (g).**  Suppose `eps < kappa` and `u` is a unitary with
`max_s ||u rho(phi(s)) u^* - rho'(s)|| < eps`.

- *If `rho` is trivial:* then `max_s ||1 - rho'(s)|| < eps < kappa`, so KD
  makes `rho'` trivial.
- *If `rho'` is trivial:* then `max_s ||rho(phi(s)) - 1|| < eps`.  KD
  applied to the homomorphism `rho o phi` makes it trivial, hence `rho` is
  trivial because `phi` is onto.  `[]`

## Step 2. Diagonal selection: approximate conjugacies give an exact representation

**Lemma D.**  Suppose that for each `j >= 1` there is a corona `C_j`, a
nontrivial homomorphism `rho_j : K -> U(C_j)`, and a unitary `u_j` in `C_j`
with `max_s ||u_j rho_j(phi(s)) u_j^* - rho_j(s)|| < 1/j`.  Then some corona
`C` carries a homomorphism `Pi : G -> U(C)` with `max_s ||Pi(s) - 1|| >= kappa`.
In particular `Pi` is nontrivial on `K x {0}`.

*Proof.*

1. **Set up lifts.**  Put `v_j = u_j^*`, so that
   `max_s ||v_j rho_j(s) v_j^* - rho_j(phi(s))|| < 1/j`.  Write
   `C_j = prod_n M_{k^j_n} / (+)`.  By (Cor2), choose unitary lifts
   `x^j_n(s)` of `rho_j(s)` for `s in S`, and `y^j_n` of `v_j`.  The quotient
   map is a `*`-homomorphism, so a word `w(x^j_n)` lifts `rho_j(w)`.
2. **Read off the coordinate estimates.**  By (Cor1):
   - `limsup_n ||r_i(x^j_n) - 1|| = ||rho_j(r_i) - 1|| = 0` for every `i`;
   - `limsup_n max_s ||y^j_n x^j_n(s) (y^j_n)^* - w_s(x^j_n)|| < 1/j`;
   - `limsup_n max_s ||x^j_n(s) - 1|| = max_s ||rho_j(s) - 1|| >= kappa`, by
     Lemma KD, since `rho_j` is nontrivial.  Here `S` is finite, so `max_s`
     commutes with `limsup_n`.
3. **Choose one coordinate per `j`.**  The first two quantities are
   eventually below `1/j`, for `i <= j`.  The third exceeds `kappa - 1/j` for
   infinitely many `n`.  So choose `n_j` at which all of the following hold:
   - `||r_i(x^j_{n_j}) - 1|| < 1/j` for `i <= j`;
   - `max_s ||y^j_{n_j} x^j_{n_j}(s) (y^j_{n_j})^* - w_s(x^j_{n_j})|| < 1/j`;
   - `max_s ||x^j_{n_j}(s) - 1|| > kappa - 1/j`.
4. **Define `Pi`.**  Let `C = prod_j M_{k^j_{n_j}} / (+)_j`, and set
   `X(s) = [(x^j_{n_j}(s))_j]` and `Y = [(y^j_{n_j})_j]`.  These are
   unitaries of `C`.
5. **Check the relations.**  By (Cor1), for each fixed `i` we get
   `||r_i(X) - 1|| <= lim_j 1/j = 0`, and likewise `Y X(s) Y^* = w_s(X)`.  By
   Step 0 this defines `Pi : G -> U(C)` with `Pi(s) = X(s)` and `Pi(t) = Y`.
6. **Check nontriviality.**
   `max_s ||Pi(s) - 1|| = limsup_j max_s ||x^j_{n_j}(s) - 1|| >= kappa`.  `[]`

This is the only place where (T) enters (a) <=> (b) <=> (c).  Without the
uniform lower bound of KD, the diagonal limit could be trivial on `K`.

## Step 3. Cyclic block shifts: a closed chain gives an approximate fixed point

**Lemma B.**  Suppose `rho_0, ..., rho_{p-1} : K -> U(C)` are homomorphisms,
at least one of them nontrivial, and `u_i` are unitaries in `C` with

```text
max_s || u_i rho_i(phi(s)) u_i^* - rho_{i+1}(s) || < eps    (indices mod p).
```

Then `rho = diag(rho_0, ..., rho_{p-1}) : K -> U(M_p(C))` is nontrivial and
satisfies `d(rho o phi, rho) < eps`.  By (Cor3), `M_p(C)` is a corona.

*Proof.*
1. Put `W = sum_i e_{i+1,i} (x) u_i`.  It is a block permutation times a
   block-diagonal unitary, so it is unitary.
2. For a block-diagonal `D = sum_i e_{ii} (x) a_i`,
   `W D W^* = sum_i e_{i+1,i+1} (x) u_i a_i u_i^*`.
3. Take `a_i = rho_i(phi(s))`.  Then `W rho(phi(s)) W^* - rho(s)` is block
   diagonal.  Its block `i+1` is `u_i rho_i(phi(s)) u_i^* - rho_{i+1}(s)`.
4. So its norm, which is the maximum over the blocks, is less than `eps` for
   every `s in S`.  `[]`

## Step 4. Assembly of (a) <=> (b) <=> (c)

- **(c) implies (b).**  Take `p = 1`.
- **(b) implies (c), with the same `eps_0`.**  A closed `eps_0`-pseudo-orbit
  of nontrivial representations is, by Lemma B, a nontrivial `rho` in the
  corona `M_p(C)` with `d(rho o phi, rho) < eps_0`.
- **(b) implies (a).**  Let `Pi : G -> U(C)` be nontrivial on `K`.  Then
  `rho = Pi|_K` is nontrivial, and `u = Pi(t)^*` gives
  `u rho(phi(s)) u^* = Pi(t)^* Pi(t) Pi(s) Pi(t)^* Pi(t) = rho(s)`.
  So `d(rho o phi, rho) = 0 < eps_0`, contradicting (b).  By (Rad), (a) holds.
- **(a) implies (b).**  If (b) fails, then for each `j` there are `C_j` and a
  nontrivial `rho_j` with `d(rho_j o phi, rho_j) < 1/j`.  Lemma D produces a
  corona representation of `G` that is nontrivial on `K`, so (a) fails.

**Proof of (f).**  Let `m >= 1` and let `rho` be nontrivial with
`d(rho o phi^m, rho) < eps_0`.

- Put `rho_i = rho o phi^i` for `0 <= i < m`, all nontrivial.
- Then `rho_i o phi = rho_{i+1}` with `u = 1` for `i < m-1`, and
  `d(rho_{m-1} o phi, rho_0) = d(rho o phi^m, rho) < eps_0`.
- So this is a closed `eps_0`-pseudo-orbit, contradicting (c).
- For `m < 0`, put `sigma = rho o phi^m`, which is nontrivial.  By symmetry
  of `d`, `d(sigma o phi^(-m), sigma) = d(rho, rho o phi^m) < eps_0`.  This
  reduces to the case `-m >= 1`.  `[]`

## Step 5. The finitary form (d), for G finitely presented

**A presentation on `S u {t}` exists.**  Finite presentability does not
depend on the finite generating set.
- Given a finite presentation `<X | R>` and a finite generating set `Y`, write
  `x = u_x(Y)` and `y = v_y(X)`.
- Tietze transformations turn this into the finite presentation
  `<Y | R(u(Y)), y = v_y(u(Y))>`.

Fix such a presentation `<S u {t} | R_G>`.  A tuple of unitaries satisfying
`R_G` in a unital C*-algebra defines a homomorphism of `G`.

- **(a) implies (d).**  Suppose (d) fails for some `theta > 0`.
  1. Then there are `sigma_j : S u {t} -> U(k_j)` with
     `max_{r in R_G} ||r(sigma_j) - 1|| < 1/j` and
     `max_s ||sigma_j(s) - 1|| >= theta`.
  2. In `C = prod_j M_{k_j} / (+)`, the classes `[(sigma_j(x))_j]` satisfy
     `R_G` exactly by (Cor1).  So they define a homomorphism `G -> U(C)`.
  3. This homomorphism has `max_s ||Pi(s) - 1|| >= theta > 0`, so it is
     nontrivial on `K`, and (a) fails.
- **(d) implies (a).**  Suppose `Pi : G -> U(C)` is nontrivial on `K`.
  1. By KD, `max_s ||Pi(s) - 1|| >= kappa`.
  2. Take unitary lifts `sigma_n` by (Cor2).  Then
     `max_r ||r(sigma_n) - 1|| -> 0`, while
     `max_s ||sigma_n(s) - 1|| > kappa/2` for infinitely many `n`, by (Cor1).
  3. This violates (d) with `theta = kappa/2`.  `[]`

Only `theta = kappa/2` is needed for (d) implies (a), so (d) with one
`theta <= kappa` is already equivalent to (d) for all `theta`.

## Step 6. Matricial stability (e)

An *asymptotic homomorphism* is a sequence `f_n : G -> U(k_n)` with
`||f_n(gh) - f_n(g) f_n(h)|| -> 0` for all `g, h`.  Matricial stability is
Dadarlat's point-norm notion, quoted verbatim in
`dadarlat-matricial-stability-obstruction`.

### (a) implies matricial stability

This uses only (a).

1. **Asymptotic triviality on `K`.**  Claim: `||f_n(k) - 1|| -> 0` for every
   `k in K`.
   - Otherwise some `k_0 in K`, some `theta > 0` and some subsequence `n_j`
     have `||f_{n_j}(k_0) - 1|| >= theta`.
   - In `C = prod_j M_{k_{n_j}} / (+)`, the map `g -> [(f_{n_j}(g))_j]` is
     multiplicative by (Cor1), so it is a homomorphism `G -> U(C)`.
   - Its value at `k_0` is at distance at least `theta` from `1`, which
     contradicts (a) through (Rad).
2. **Unitality and powers.**
   - `||f_n(1) - 1|| = ||f_n(1)^* (f_n(1) f_n(1) - f_n(1))|| -> 0`.
   - Hence `f_n(t^-1) f_n(t) -> 1`.  By induction on `|m|`,
     `||f_n(t^m) - v_n^m|| -> 0` for each fixed `m`, where `v_n = f_n(t)`.
3. **The genuine homomorphisms.**  Define `pi_n(k t^m) = v_n^m`.  This is a
   homomorphism `G -> Z -> U(k_n)`.  For fixed `g = k t^m`,

```text
||f_n(g) - pi_n(g)|| <= ||f_n(k t^m) - f_n(k) f_n(t^m)|| + ||f_n(k) - 1|| + ||f_n(t^m) - v_n^m|| -> 0.
```

### Matricial stability implies (a), when K is finitely generated and quotientless

1. By `matricial-stability-identifies-radicals`, `Rad_MF(G) = Rad_fd(G)`,
   the finite-dimensional unitary residual.
2. Let `pi` be a finite-dimensional unitary representation of `G`.
   - `pi(K)` is a finitely generated linear group, so it is residually finite
     by (Mal).
   - It is a quotient of `K`, which has no nontrivial finite quotient, so
     `pi(K) = 1`.
3. Hence `K x {0} <= Rad_fd(G)`.  With (Rad) this gives
   `Rad_MF(G) = Rad_fd(G) = K x {0}`.  `[]`

## Step 7. The flagship consequence

Let `(G,K)` be a witness of `torsion-free-sofic-exact-mf-radical-over-z`.

1. `G/K = Z` is free, so `G = K semidirectProduct_phi Z` for some
   automorphism `phi` of `K`.
2. `K` has (T), so it is finitely generated (KP).
3. `mapping-torus-mf-radical-lies-in-finite-residual` (FRB1) gives
   `K x {0} = Rad_MF(G) <= R_fin(K) x {0}`, so `K` has no nontrivial finite
   quotient.
4. Step 6 then shows that `G` is matricially stable.

Conversely, suppose `G` is a finitely presented, torsion-free, sofic,
matricially stable group `K semidirectProduct_phi Z`, with `K` a nontrivial
Kazhdan group and no nontrivial finite quotient.  Then the converse half of
Step 6 gives `Rad_MF(G) = K x {0}`, so `G` is a witness.

The kills (K1)--(K3) in the claim follow directly:

- (K1) is (f) contraposed.
- (K2) is pigeonhole plus the identity `rho o phi^b = (rho o phi^a) o phi^(b-a)`,
  so no Lipschitz loss occurs.
- (K3) is (c) read as a statement about periodization.  `[]`
