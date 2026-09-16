# Anti-central swap fullness gives projective swap fullness, so the ternary swap corner is one half

Lane `swarm-ternary-leavitt-swap-idempoten`, 2026-09-16. Target: `ternary-leavitt-swap-idempotent-is-full`.

This artifact proves an implication. It decides neither half.

- **Theorem 5.** A solution of the anti-central corner equation in `S_-` produces explicit witnesses of the
  projective corner equation in `F_3[PG]`.
- **Corollary 6.2.** The target claim is therefore equivalent to its anti-central half
  `ternary-anti-invariant-swap-corner-is-full`.
- **Proposition 7.1.** Thompson's `V` embeds in `L_(F_3)(1,2)^x`, with its first-letter swap going to `w`.
  So `thompson-v-ternary-swap-idempotent-is-full` implies the target.

Script: `experiments/ternary-swap-fullness-equivalence-2026-09-16/verify_identities.py` (Section 9).

## 0. Setting

- **Field and algebra.** `k = F_3`, so `2 = -1 = 1/2`. `R = L_k(1,2)` has generators `s0, s1, t0, t1`
  with `t_i s_j = delta_ij` and `s0 t0 + s1 t1 = 1`.
- **Groups.** `G = R^x`, `z = -1`, `PG = G/<z>`, and `gbar` is the image of `g`.
- **Group algebras.** `S = k[G]`, `eps_(+-) = 2(1 +- [z])`, `S_(+-) = eps_(+-) S`, `A = k[PG]`.
- **The identification.** By Lemma 7.1 of `invariant-output-descent-and-sensitivity-2026-09-12.md`, the map
  `theta : A -> S_+`, `[gbar] -> eps_+ [g]`, is a unital ring isomorphism. It is well defined because
  `eps_+ [z] = eps_+`.
- **Elements.**
  - `w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `h = s0 t0 + s0 t1 + s1 t0 - s1 t1`.
  - `e = 2(1 + [w])` and `e_- = eps_- e` in `S`.
  - `e_w = 2(1 + [wbar])` in `A`; this is `ebar` of `projective-ternary-swap-idempotent-is-full`.

**Murray-von Neumann order.** For idempotents `p, q` of a ring `A`, write `p <~ q` if there are
`x in qAp` and `y in pAq` with `yx = p`. The following standard facts are used, each with its one-line proof.

- (MvN1) If `pq = qp = p`, then `p <~ q` via `x = y = p`.
- (MvN2) If `p <~ q` via `(x, y)` and `q <~ r` via `(x', y')`, then `p <~ r` via `(x'x, yy')`, since
  `y y' x' x = y q x = yx = p`.
- (MvN3) `1 <~ e_w` iff some `b, c in A` satisfy `c e_w b = 1`. From `(x, y)` take `b = x`, `c = y`. Conversely
  take `x = e_w b`, `y = c e_w`.

## 1. The chart, the Hadamard unit and the block-diagonal homomorphism

**Lemma 1.**

(a) `a -> (t_i a s_j)_(i,j)` is a ring isomorphism `R -> M_2(R)` with inverse `(a_ij) -> sum s_i a_ij t_j`.

(b) In this chart:
- `w = [[0,1],[1,0]]`, `d = diag(1,-1)` and `h = [[1,1],[1,-1]]`.
- Hence `w^2 = d^2 = 1`, `d w d = z w`, `h^2 = z`, `h w h^-1 = d` and `h d h^-1 = w`.

(c) Define `mu(g_1, g_2) = s0 g_1 t0 + s1 g_2 t1`, the chart matrix `diag(g_1, g_2)`.
- `mu : G x G -> G` is an injective group homomorphism.
- `mu(z, 1) = z d`, `mu(1, z) = d` and `mu(z, z) = z`.
- `w mu(g_1, g_2) w = mu(g_2, g_1)`.

*Proof.*

(a) The products compose correctly: `sum_k (t_i a s_k)(t_k b s_j) = t_i a (sum_k s_k t_k) b s_j = t_i ab s_j`.
The inverse is two-sided: `sum_(i,j) s_i t_i a s_j t_j = a`, and `t_i (sum s_k a_kl t_l) s_j = a_ij`.

(b) Read off `t_i x s_j`. For example `t0 w s1 = t1 s1 = 1` and `t0 w s0 = t1 s0 = 0`. The rest are
products of `2 x 2` matrices over `F_3 <= R`:
- `h^2 = 2I = -I`;
- `h w h = -d`, so `h w h^-1 = h w (-h) = d`;
- `h d h = -w`, so `h d h^-1 = w`.

(c) Multiplicativity follows from `t_i s_j = delta_ij`:

    mu(g_1,g_2) mu(g_1',g_2') = s0 g_1 g_1' t0 + s1 g_2 g_2' t1,

and `mu(1,1) = s0 t0 + s1 t1 = 1`. Injectivity holds because the chart entries recover `g_1, g_2`.

The values at `z` are `mu(z,1) = -s0 t0 + s1 t1 = -d`, `mu(1,z) = d` and `mu(z,z) = -1`.

For the flip, use `w s0 = s1`, `w s1 = s0`, `t0 w = t1` and `t1 w = t0`. These give
`w mu(g_1,g_2) w = s1 g_1 t1 + s0 g_2 t0 = mu(g_2, g_1)`. QED

## 2. Klein and Hadamard idempotents in `A = k[PG]`

By Lemma 1(b), `wbar` and `dbar` are commuting involutions of `PG`. For `a, b in {+,-}` put

    q_ab = 2(1 + a[wbar]) . 2(1 + b[dbar]),   f = 2(1 - [dbar]),   H = [hbar].

**Lemma 2.**

(a) The `q_ab` are pairwise orthogonal commuting idempotents with `sum q_ab = 1`.

(b) `e_w = q_++ + q_+-`, `f = q_+- + q_--`, `f e_w = e_w f = q_+-` and `2 e_w = 1 + [wbar]`.

(c) `H^2 = 1`, `H [wbar] H = [dbar]` and `H [dbar] H = [wbar]`. Hence `H q_ab H = q_ba`.

(d) Put `u = H q_-+` and `v = q_-+ H`. Then `u = q_+- H`, so `u in q_+- A q_-+`. Also `v in q_-+ A q_+-` and
`vu = q_-+`.

*Proof.*

(a), (b) The elements `2(1 +- [x])` for an involution `x` are complementary idempotents:
`(2(1 + [x]))^2 = 4 . 2(1 + [x]) = 2(1 + [x])`, and the two sum to `4 = 1`. Products of such pairs for two
commuting involutions give (a). For (b), `q_++ + q_+- = 2(1 + [wbar]) . (2(1 + [dbar]) + 2(1 - [dbar]))`.
The same computation gives `f`, and `2 e_w = 4(1 + [wbar]) = 1 + [wbar]`.

(c) `hbar^2 = zbar = 1`, and Lemma 1(b) passes to `PG`.

(d) `H q_-+ H = q_+-` and `H^2 = 1` give `H q_-+ = q_+- H`. Hence `q_+- u = u = u q_-+`, and similarly for `v`.
Finally `vu = q_-+ H H q_-+ = q_-+`. QED

## 3. The tensor map

Identify `k[G] (x) k[G] = k[G x G]` and define

    Psi_0 : k[G] (x) k[G] -> A,   [g_1] (x) [g_2] -> [ mu(g_1, g_2) mod z ].

**Lemma 3.**

(a) `Psi_0` is a unital ring homomorphism.

(b) `Psi_0(eps_- (x) 1) = Psi_0(1 (x) eps_-) = f`.
- Hence `Psi_0(eps_- (x) eps_-) = f`, and `f` commutes with the image of `Psi_0`.
- `S_- (x) S_- = (eps_- (x) eps_-)(k[G] (x) k[G])` is a unital ring with unit `eps_- (x) eps_-`.
- The restriction `Psi` of `Psi_0` to it is a unital ring homomorphism `S_- (x) S_- -> fAf`.

(c) `[wbar] Psi_0(x (x) y) [wbar] = Psi_0(y (x) x)` for all `x, y in k[G]`.

*Proof.*

(a) `Psi_0` is the linear extension of the group homomorphism `G x G -> G -> PG` given by `mu` followed
by the quotient map.

(b) By Lemma 1(c), `mu(z,1) = zd` and `mu(1,z) = d`, and both have image `dbar`. So
`Psi_0(eps_- (x) 1) = 2([1] - [dbar]) = f`, and likewise for `1 (x) eps_-`.

`eps_- (x) eps_- = (eps_- (x) 1)(1 (x) eps_-)` is central in `k[G x G]`. Its image `f . f = f` therefore
commutes with the image of `Psi_0`, and `Psi_0` maps `(eps_- (x) eps_-) k[G x G]` into `fAf`, unit to unit.
The tensor product over a field of subspaces injects, so `S_- (x) S_-` is a subring.

(c) On basis elements this is Lemma 1(c) modulo `z`, using `wbar^-1 = wbar`. Then extend bilinearly. QED

## 4. The Cohn family of a corner solution

**Lemma 4.** `e_- [d] e_- = 0` in `S`.

If `b_-, c_- in S_-` satisfy `c_- e_- b_- = eps_-`, put

    beta_1 = e_- b_-,   beta_2 = [d] e_- b_-,   gamma_1 = c_- e_-,   gamma_2 = c_- e_- [d].

These lie in `S_-`, and `gamma_i beta_j = delta_ij eps_-`.

*Proof.* Lemma 7.2 of the 2026-09-12 artifact gives `[d] e_- [d] = eps_- - e_-`, and `[d]^2 = 1`. Hence

    e_- [d] e_- = [d]([d] e_- [d]) e_- = [d](eps_- - e_-) e_- = 0.

The products are:
- `gamma_1 beta_1 = c_- e_- b_- = eps_-`;
- `gamma_2 beta_2 = c_- e_- [d][d] e_- b_- = eps_-`;
- `gamma_1 beta_2 = gamma_2 beta_1 = c_- e_- [d] e_- b_- = 0`.

Membership in `S_-` holds because `eps_-` is central. QED

## 5. The theorem

**Theorem 5.** Let `b_-, c_- in S_-` satisfy `c_- e_- b_- = eps_-`, and take `beta_i, gamma_i` from Lemma 4.
In `A = F_3[PG]` put

    X_i = Psi(beta_i (x) eps_-),   Y_i = Psi(gamma_i (x) eps_-),   X = Psi(beta_1 (x) beta_2),   Y = Psi(gamma_1 (x) gamma_2),

and

    b = q_++ + e_w X (X_1 H q_-+ + X_2),
    c = q_++ + 2 (q_-+ H Y_1 + Y_2) Y e_w.

Then `e_w b = b`, `c e_w = c` and `c b = 1`. In particular `c ebar b = 1`, so
`projective-ternary-swap-idempotent-is-full` holds.

*Proof.*

**Step 1 (relations).** By Lemma 3(b), all of `X_i, Y_i, X, Y` lie in `fAf`. By Lemmas 3 and 4:
- `Y_i X_j = Psi(gamma_i beta_j (x) eps_-) = delta_ij f`.
- `Y X = Psi(gamma_1 beta_1 (x) gamma_2 beta_2) = Psi(eps_- (x) eps_-) = f`.
- By the flip, Lemma 3(c), `[wbar] X [wbar] = Psi(beta_2 (x) beta_1)`. So

      Y [wbar] X = Psi(gamma_1 (x) gamma_2) Psi(beta_2 (x) beta_1) [wbar] = Psi(gamma_1 beta_2 (x) gamma_2 beta_1) [wbar] = 0.

**Step 2 (`f <~ q_+-`).** Put `x_B = e_w X` and `y_B = 2 Y e_w`.
- Since `X = fX` and `e_w f = q_+-`, we have `x_B = q_+- X in q_+- A f`, and likewise `y_B = 2 Y q_+- in f A q_+-`.
- Using `e_w^2 = e_w` and `2 e_w = 1 + [wbar]`,

      y_B x_B = 2 Y e_w X = Y (1 + [wbar]) X = YX + Y [wbar] X = f.

**Step 3 (`q_-+ + f <~ f`).** Note `q_-+ f = f q_-+ = 0`. With `u, v` from Lemma 2(d) put

    x' = X_1 u + X_2,   y' = v Y_1 + Y_2.

- **Membership.** `x' in f A (q_-+ + f)` because `X_1 u in f A q_-+` and `X_2 in fAf`. Likewise `y' in (q_-+ + f) A f`.
- **Product.** By Step 1,

      y' x' = v (Y_1 X_1) u + v (Y_1 X_2) + (Y_2 X_1) u + Y_2 X_2 = v f u + f.

- **Conclusion.** `fu = u`, since `u = q_+- u` and `f q_+- = q_+-`. So `y' x' = vu + f = q_-+ + f`.

**Step 4 (assembly).** Put `x'' = x_B x'` and `y'' = y' y_B`.
- `x'' in q_+- A (q_-+ + f)` and `y'' in (q_-+ + f) A q_+-`.
- `y'' x'' = y' (y_B x_B) x' = y' f x' = y' x' = q_-+ + f`, since `x' = f x'`.
- Expanding `u = H q_-+` and `v = q_-+ H` shows `b = q_++ + x''` and `c = q_++ + y''`.

Now:
- `e_w q_++ = q_++` and `e_w x'' = e_w q_+- x'' = x''`, so `e_w b = b`. Symmetrically `c e_w = c`.
- The cross terms of `c b` vanish: `q_++ x'' = q_++ q_+- x'' = 0` and `y'' q_++ = y'' q_+- q_++ = 0`.
- Hence `c b = q_++ + y'' x'' = q_++ + q_-+ + q_+- + q_-- = 1`, and `c e_w b = c b = 1`. QED

**Remark 5.1 (what is used).** The proof uses only:
1. a unital homomorphism `Psi : S_- (x) S_- -> fAf` with the flip property;
2. the Klein and Hadamard relations of Lemma 2;
3. the Cohn family of Lemma 4.

In particular `Psi` never needs to be injective, and no property of `PG` beyond `mu` and `h` enters.

**Remark 5.2 (the mechanism).** Step 1 already shows that `f` is properly infinite in `A`, since
`Y_i X_j = delta_ij f` with `X_i, Y_i in fAf`. Two more things are needed to reach `1 <~ e_w`.
- **The swap-separated pair `(X, Y)`.** This is where the flip enters. It pushes `f` below `q_+- = f e_w`
  (Step 2).
- **The Hadamard involution.** It moves the sector `q_-+`, which lies outside both `f` and `e_w`, onto
  `q_+-` inside `f`, where the Cohn family absorbs it (Step 3).

The sector `q_++` is already inside `e_w`, so it is carried by the identity.

## 6. Corollaries

**Corollary 6.1 (gluing).** Suppose `b_-, c_- in S_-` satisfy `c_- e_- b_- = eps_-`, and `b, c in A` satisfy
`c e_w b = 1`. Then `B = theta(b) + b_-` and `C = theta(c) + c_-` satisfy `C e B = 1` in `S`.

*Proof.* `e = eps_+ e + eps_- e = theta(e_w) + e_-`. Products between `S_+` and `S_-` vanish, because
`eps_+ eps_- = 0` and both are central. So

    C e B = theta(c) theta(e_w) theta(b) + c_- e_- b_- = theta(1) + eps_- = eps_+ + eps_- = 1.

QED

**Corollary 6.2 (equivalence).** The following are equivalent.

1. `ternary-leavitt-swap-idempotent-is-full`: `c e b = 1` is solvable in `F_3[G]`.
2. `ternary-anti-invariant-swap-corner-is-full`: `c_- e_- b_- = eps_-` is solvable in `S_-`.

When they hold, `projective-ternary-swap-idempotent-is-full` holds too.

*Proof.*
- (1 => 2) Multiply by `eps_-`. This is the existing route `ternary-swap-fullness-projects-to-anti-invariant-half`.
- (2 => 1) Theorem 5 gives `b, c in A`, and Corollary 6.1 glues them to `b_-, c_-`.

The explicit witness is

    B = theta(q_++ + e_w X (X_1 H q_-+ + X_2)) + b_-,
    C = theta(q_++ + 2(q_-+ H Y_1 + Y_2) Y e_w) + c_-.

QED

**Corollary 6.3 (consequences for the graph).** These are logical consequences only. No committed node is edited.

(a) **Shared refuters.** The two claims are equivalent, so they have the same refuters.
- The refuters of the anti-central half already refute the target, through the existing projection route.
  These include:
  - a nontrivial characteristic-three rank model of `G` (`ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`);
  - relative positivity of the lifted trace (`anti-central-lifted-trace-is-relatively-positive`), that is, a
    `K_0` state on `(K_0(S_-), [eps_-])`.
- The new direction is the converse. Anything that refutes the target also refutes the anti-central half,
  and with it `ternary-anti-central-summand-has-cohn-family`, which the existing two-route cycle makes
  equivalent to that half.

(b) **A new refuter of the anti-central half.** `projective-ternary-swap-idempotent-is-not-full` refutes it,
by the contrapositive of Theorem 5. So does `projective-ternary-group-is-f3-linear-sofic`, directly: that node
already notes that it kills both halves.

(c) **The halves are not independent.** Part 6 of `ternary-leavitt-swap-problem-splits-at-central-involution`
says that either half suffices for nonsurjunctivity. Theorem 5 says the Leavitt-visible half is at least as
strong as the Leavitt-invisible half. A search should therefore target `S_-`, or the Cohn-family form. A
solution on `PG` alone is weaker, and it is not known to give the target (Section 8.1).

## 7. Thompson's group `V` inside the ternary unit group

**Proposition 7.1.** Let `Omega = {0,1}^N` and `k^(Omega)` the vector space with basis `e_xi`, `xi in Omega`.

1. The operators `s_i e_xi = e_(i xi)` and `t_i e_(j xi) = delta_ij e_xi` define an injective unital ring
   homomorphism `pi : R -> End_k(k^(Omega))`.
2. Take `g in V` given by complete prefix codes `(a_1, ..., a_n) -> (b_1, ..., b_n)`, that is,
   `g(a_i eta) = b_i eta`. Put `u_g = sum_i s_(b_i) t_(a_i)`, where `s_(x_1...x_m) = s_(x_1) ... s_(x_m)` and
   `t_(x_1...x_m) = t_(x_m) ... t_(x_1)`. Then `pi(u_g) e_xi = e_(g(xi))`.
3. `u_g` depends only on `g`, and `g -> u_g` is an injective group homomorphism `V -> G`.
4. The first-letter swap `w_V`, with codes `(0,1) -> (1,0)`, maps to `w`.

*Proof.*

(1) The relations hold on basis vectors:
- `t_i s_j e_xi = t_i e_(j xi) = delta_ij e_xi`;
- `(s0 t0 + s1 t1) e_(j xi) = s_j e_xi = e_(j xi)`.

So `pi` is a unital homomorphism, and it is nonzero. `R` is simple (`leavitt-algebras-l-k-1-n-are-simple`),
so `ker pi = 0`.

(2) By induction on `|a|`, `t_a e_xi = e_eta` if `xi = a eta`, and `0` otherwise. Also `s_b e_eta = e_(b eta)`.
The code `{a_i}` is complete, so exactly one `a_i` is a prefix of `xi`, and `pi(u_g) e_xi = e_(g(xi))`.

(3) `pi(u_g)` is the permutation operator `P_g`, which depends only on `g`. Since `pi` is injective, so does
`u_g`. From `P_(g o g') = P_g P_(g')` and `P_1 = id` we get `u_(g o g') = u_g u_(g')` and `u_1 = 1`. So
`u_g in G`, and the map is a homomorphism. It is injective because `P_g != id` for `g != 1`. If `V` is
composed in the opposite order, use `g -> u_(g^-1)` instead; this changes nothing below, since `w_V` is an
involution.

(4) `u_(w_V) = s1 t0 + s0 t1 = w`. QED

**Corollary 7.2.** If `c e_V b = 1` in `F_3[V]` with `e_V = 2(1 + [w_V])`, then the induced unital ring
homomorphism `F_3[V] -> F_3[G]` gives `c' e b' = 1`. So `thompson-v-ternary-swap-idempotent-is-full` implies
`ternary-leavitt-swap-idempotent-is-full`, as its `distinct_from` entry anticipates. No route recorded this
before.

## 8. What is not derived

**8.1 Projective to anti-central.** The converse of Theorem 5 is not proved.

*A sufficient condition.* Suppose there is a group homomorphism `phi : PG -> G` with `phi(wbar) != +-1`. Then
`[gbar] -> eps_- [phi(gbar)]` is a unital ring homomorphism `A -> S_-`. It sends `e_w` to
`eps_- 2(1 + [x])` with `x = phi(wbar)`, an involution different from `+-1`.

Conjugacy to `w` would finish the argument.
- An involution `x` of `R` is `2p - 1` with `p = 2(1 + x)` idempotent, and `p != 0, 1` when `x != +-1`.
- By the Ara-Moreno-Pardo computation `V(L_K(1,2)) = {0, [1]}`, every nonzero idempotent of `R` is equivalent
  to `1`. So any two idempotents `p, q` different from `0` and `1` are conjugate: `p ~ 1 ~ q`, and
  `1 - p ~ 1 ~ 1 - q` since the complements are nonzero too. This is imported and was not re-verified here.
- Hence `x` is conjugate to `w`, and conjugating the image of a projective solution gives an anti-central
  solution.

*Status of the condition.* No such `phi` is known.
- `mu`, the diagonal `delta(g) = mu(g,g)` and the corner maps `mu(g,1)`, `mu(1,g)` all send `z` to
  `z`, `zd` or `d`. So they do not factor through `PG`.
- A homomorphism `g -> Theta(g (x) (g^-1)^op)` would come from a unital homomorphism
  `Theta : R (x) R^op -> R`. Note that `R^op ~= R` through the involution `s_i <-> t_i`. The homomorphism
  kills `z`, since `z (x) z^op = 1`, and it sends `wbar` to the involution `Theta(w (x) w^op)`.
- Whether such a unital map `L_K(1,2) (x) L_K(1,2) -> L_K(1,2)` exists over a field is Question 5.7 of
  Ara-Cortinas (arXiv:1108.0352v3). That attribution is taken from the graph node
  `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`, where the question is recorded as open; it
  was not re-read here.
- Brownlowe-Sorensen, arXiv:1603.03618 (title checked on the arXiv API on 2026-09-16), show that
  `L_(2,Z) (x) L_(2,Z)` does not embed in `L_(2,Z)` over `Z`.
- Even given `Theta`, the image of `wbar` would still have to differ from `+-1`.

*A ring map that does exist, and why it does not help.* Put `p' = eps_- 2(1 - [d])` and
`p'' = eps_- 2(1 + [d])`. These are orthogonal idempotents with `p' + p'' = eps_-`, and they commute with
every `[mu(g_1,g_2)]`, since `d = mu(1,z)`. Define

    Phi : A -> S_-,   [gbar] -> p' [mu(g,1)] + p'' [mu(1,g)].

- **Well defined.** `mu(z,1) = zd`, and `p' [z][d] = p'`. Also `mu(1,z) = d`, and `p'' [d] = p''`.
- **A ring map.** The cross terms vanish, because `p' p'' = 0` and both commute with the diagonal units.
  So `Phi` is a unital ring homomorphism into `S_-`, although it does not come from a group homomorphism
  `PG -> G`.
- **What the projective half gives.** `c e_w b = 1` gives `eps_- <~ Phi(e_w)` in `S_-`.
- **What is missing.** To reach the anti-central half, one needs the comparison `Phi(e_w) <~ e_-`.
  - That comparison follows from the anti-central half, by (MvN1) and (MvN2).
  - So, given the projective half, it is *equivalent* to the anti-central half. This is a restatement,
    not a reduction.
- **Leavitt-invisible.** The Leavitt evaluation `pi : S -> R` sends `p'` to `s1 t1`, `p' [mu(g,1)]` to
  `s1 t1`, and `p'' [mu(1,g)]` to `s0 t0`. So `pi o Phi` is the augmentation `A -> F_3`. In particular
  `pi(Phi(e_w)) = 1`. Under `pi`, the missing comparison becomes `1 <~ 2(1 + w)` in `R`, which the Leavitt
  solution `b = s0 + s1`, `c = 2(t0 + t1)` already provides. So the evaluation gives no obstruction and no
  information.
- **Checked.** `experiments/ternary-swap-fullness-equivalence-2026-09-16/verify_corner_map.py` printed 43
  `PASS` lines (`output_corner_map.txt`). It checks well-definedness, multiplicativity, unitality and the
  evaluation on the finite subgroup `Q` of order 16.

**8.2 Klein fullness.** Theorem 5 does not give `projective-ternary-klein-idempotent-is-full`. The
construction carries `q_++` by the identity. Every partial isometry it builds lives between `q_-+`, `q_+-`
and `f`, and the images of `Psi` lie in `fAf` with `f q_++ = 0`. Nothing here moves mass into `q_++`.

**8.3 Invariants.** Theorem 5 is consistent with all the invariants of `F_3[PG]` recorded in the graph:
- the identity-coefficient trace;
- Hattori-Stallings ranks;
- two-sided fullness;
- the augmentation, which vanishes on `f` and on the images of `Psi`.

It adds no new obstruction.

## 9. Script

`experiments/ternary-swap-fullness-equivalence-2026-09-16/verify_identities.py`, run under `timeout 600`,
printed 131 `PASS` lines. The output is in `output.txt` in the same directory. The map `Phi` of Section 8.1
is checked separately, as described there.

- **Part A.** The finite subgroup `Q = <w, d, h>` of `G`, of order 16, embedded through the chart as scalar
  matrices. It checks:
  - the chart relations of Lemma 1(b);
  - `[d] e_- [d] = eps_- - e_-` and `e_- [d] e_- = 0` in `F_3[Q]`;
  - `c e_- [d] e_- b = 0` for random `b, c`;
  - all of Lemma 2 in `F_3[Q/{+-1}]`.
- **Part B.** The restriction of `Psi_0` to `Q x Q`, through the depth-2 chart. It checks:
  - `mu` multiplicative;
  - `w mu(g_1,g_2) w = mu(g_2,g_1)`;
  - `Psi_0(eps_- (x) 1) = Psi_0(1 (x) eps_-) = f`;
  - multiplicativity and the flip on random tensors;
  - `H [wbar] H = [dbar]`.
- **Part C.** An operator model on a space with basis `(Klein sector, n)`. In it, every hypothesis of
  Step 1 holds: `Y_i X_j = delta_ij f`, `YX = f`, `Y[wbar]X = 0`, membership in `fAf`, and the Klein and
  Hadamard relations. It checks `e_w b = b`, `c e_w = c` and `cb = 1` for the displayed formulas, on 160
  basis vectors. This guards against typos in `b` and `c`. It is not a universal model and does not
  replace the proof.
