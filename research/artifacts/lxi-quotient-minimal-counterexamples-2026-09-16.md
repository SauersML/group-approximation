# Quotient-minimal counterexamples to LXI: prime case or undetected loops

Swarm lane `swarm-stw99-problem-lxi-properly-inf`, 2026-09-16. The results below have complete proofs
here. Nobody outside this lane has reviewed them, and they do not decide STW Problem LXI. Proposition 1
and the first half of Proposition 2 are due to R. Rohde (PhD thesis, IMADA, University of Southern
Denmark, March 2009, supervisor M. Rørdam, Lemmas 5.1.6--5.1.8 and the proof of Lemma 5.2.3). They are reproved here in the properly infinite setting,
where the weak K0-surjectivity hypothesis of Lemma 5.1.8 holds automatically. Theorem 3 and
Corollaries 4--5 were not found in the sources listed in Section 6.

## 0. Conventions and standard facts

C\*-algebras are unital unless stated otherwise, and ideals are closed and two-sided. `U(A)` is the
unitary group and `U_0(A)` its identity component. `q_J: A -> A/J` is the quotient map.

- A **witness** is a pair `(A, u)`: `A` unital properly infinite, `u in U(A)`, `[u] = 0` in `K_1(A)`,
  and `u notin U_0(A)`. LXI says no witness exists.
- A witness `(B, v)` is **quotient-minimal** if `q_J(v) in U_0(B/J)` for every nonzero ideal `J` of `B`.
- `B` is **prime** if any two nonzero ideals of `B` have nonzero intersection.
- `SE = C_0((0,1), E)`. A *based loop* in `U(M_n(E))` is a continuous `a: [0,1] -> U(M_n(E))` with
  `a(0) = a(1) = 1`. Then `a - 1 in M_n(SE)`, and `â = 1 + (a - 1)` is a unitary in `M_n((SE)~)`.
  Put `kappa_E(a) = [â]_1 in K_1(SE)`. A loop is *undetected* if `kappa_E(a) = 0` but `a` is not
  homotopic to the constant loop relative to `{0,1}`.

Standard facts used below:

(F1) If `Phi: P -> Q` is a surjective unital \*-homomorphism, then `Phi(U_0(P)) = U_0(Q)`. Every element
of `U_0(Q)` is a finite product of `exp(i h_j)` with `h_j` self-adjoint. Lift each `h_j` to a
self-adjoint element of `P`.

(F2) If `x in U(Q)` and `||x - 1|| < 2`, then `x in U_0(Q)`, because `-1 notin sp(x)` and `x = exp(i h)`
with a continuous logarithm.

(F3) In a topological group, concatenation `a * b` of based loops is based-homotopic to the pointwise
product `ab`. The reverse loop `ā` inverts `a`, and `pi_1` is abelian. Two paths `alpha, beta` from 1 to
`d` are homotopic relative to endpoints iff the loop `alpha * beta̅` is null. `kappa_E` is a group
homomorphism on `pi_1(U(M_n(E)), 1)`. It is natural under unital \*-homomorphisms, and
`kappa_E(diag(a, 1_{m})) = kappa_E(a)`.

(F4) Let `G` be a topological group and `a` a based loop. If `a` is homotopic to the constant 1 through
arbitrary maps `H_lambda: T -> G`, then `(z, lambda) -> H_lambda(z) H_lambda(1)^{-1}` is a based
null-homotopy. So for the unitary `a in C(T, E)`: `a in U_0(C(T, E))` iff `a` is based null-homotopic.

(F5) Let `E` be unital properly infinite. Every `x in K_1(SE)` equals `kappa_E(mu_e)` for a projection
`e in E`, where `mu_e(t) = exp(2 pi i t) e + (1 - e)` is a based loop in `U(E)`. Proof: the Bott map
`beta_E: K_0(E) -> K_1(SE)`, `[p]_0 -> [z p + (1 - p)]_1`, is an isomorphism (Bott periodicity;
Rordam--Larsen--Laustsen, *An Introduction to K-Theory for C\*-Algebras*, CUP 2000, Chapter 11; theorem
number not rechecked). Every `g in K_0(E)` is `[e]_0` for a projection `e in E`
(Blanchard--Rohde--Rordam arXiv:0704.1554v1, Proposition 2.3(ii), due to Cuntz). Finally
`z e + (1 - e) = mu_e^`.

(F5') *Referee addendum (2026-09-16): a self-contained proof of the part of (F5) that is used,
without Bott periodicity.* Let `E` be unital properly infinite. Every `x in K_1(SE)` equals
`kappa_E(b)` for some based loop `b` in `U(E)`. Proof. Write `x = [w]_1` with `w in U_n((SE)~)`. The
scalar part `s(w) in U_n(C)` is connected to 1, so replacing `w` by `w s(w)^*` we may assume
`w - 1 in M_n(SE)`. Then `a = w` is a based loop in `U(M_n(E))` with `â = w`. Take isometries
`t_1, t_2 in E` with `t_1^* t_2 = 0` and put `s_j = t_1^{j-1} t_2` (`j = 1, ..., n`). For `k < m`,
`s_k^* s_m = t_2^* t_1^{m-k} t_2 = 0`, so the `s_j` are isometries with pairwise orthogonal ranges. Let
`V = (s_1, ..., s_n) in M_{1,n}(E)`, so `V^* V = 1_n`, and let `q = V V^*`. The matrix
`U = [[V, 1 - q], [0_n, V^*]] in M_{n+1}(E)` is unitary, and a direct computation gives
`U diag(a(t), 1) U^* = diag(b(t), 1_n)` with `b(t) = V a(t) V^* + (1 - q)`, a based loop in `U(E)`.
Conjugation by the constant unitary `U` does not change the `K_1(SE)` class. Take a path `W_s` in
`U(M_{2n+2}(E))` from 1 to `diag(U, U^*)` (Whitehead). Then `s -> W_s diag(â, 1) W_s^*` is a path of
unitaries in `M_{2n+2}((SE)~)`, because `SE` is an ideal in `C([0,1], E)`. It runs from `diag(â, 1)` to
`diag(b̂, 1_n, 1_{n+1})`. Hence `kappa_E(b) = [â]_1 = x`. Square.

(F6) For ideals `J_1, J_2` of `B`, let `B_i = B/J_i`, `D = B/(J_1 + J_2)`, and let `pi_i: B_i -> D` be the
induced maps. If `J_1 ∩ J_2 = 0`, then `b -> (q_{J_1} b, q_{J_2} b)` is a \*-isomorphism of `B` onto
`{(x, y) in B_1 (+) B_2 : pi_1 x = pi_2 y}`. It is injective because its kernel is `J_1 ∩ J_2`. For
surjectivity, lift `x = q_{J_1}(a)` and `y = q_{J_2}(b)`. Then `a - b in J_1 + J_2`; write
`a - b = j_1 + j_2` and take `c = a - j_1 = b + j_2`. (`J_1 + J_2` is closed.) So a continuous path in
`U(B)` is a pair of paths `(g_1, g_2)` in `U(B_1)` and `U(B_2)` with `pi_1 g_1 = pi_2 g_2` pointwise.

## 1. Quotient-minimal quotients (Rohde)

**Proposition 1.** If `(A, u)` is a witness, then there is an ideal `I` of `A` such that
`(A/I, q_I(u))` is a quotient-minimal witness.

*Proof.* Let `S` be the set of ideals `I` with `q_I(u) notin U_0(A/I)`, ordered by inclusion. It
contains `0`. Let `C` be a nonempty chain in `S` and `J` the closure of its union, an ideal. Suppose
`q_J(u) in U_0(A/J)`. By (F1) there is `w in U_0(A)` with `q_J(w) = q_J(u)`, so `y = w^* u in 1 + J`.
Since the union of the chain is dense in `J` and the chain is increasing, some `I in C` has
`||q_I(y) - 1|| = dist(y - 1, I) < 1`. By (F2), `q_I(y) in U_0(A/I)`, hence `q_I(u) = q_I(w) q_I(y) in
U_0(A/I)`, which contradicts `I in S`. So `J in S`. By Zorn's lemma `S` has a maximal element `I`.

`B = A/I` is nonzero, because `q_I(u) notin U_0`. It is properly infinite, as the images of two isometries
with orthogonal ranges remain such. `[q_I(u)] = q_{I*}[u] = 0`. The nonzero ideals of `B` are `I'/I` with
`I' ⊋ I`, and `B/(I'/I) = A/I'`. Maximality gives `q_{I'}(u) in U_0(A/I')`. Square.

## 2. Moving the witness into any ideal

**Proposition 2.** Let `(B, v)` be a quotient-minimal witness and `J` a nonzero ideal of `B`.
(a) There is `v_J in U(J~)`, `J~ = J + C1 subset B`, with `v ~_h v_J` in `U(B)` and
`[v_J]_{K_1(J)} = 0`. In particular `v_J notin U_0(J~)`, so `J~` is not K1-injective.
(b) For any unital \*-homomorphism `sigma: T_2 -> B` (one exists since `B` is properly infinite),
`C = J + sigma(T_2)` is a unital C\*-subalgebra, and `(C, v_J)` is a witness. `C/J` is a quotient of
`T_2`.
(c) `B` has no central projection other than 0 and 1. Every nonzero ideal `J` is non-stable, and
`J~` does not have stable rank one.

*Proof.* (a) `q_J(v) in U_0(B/J)`. By (F1) take `w in U_0(B)` with `q_J(w) = q_J(v)`, and put
`v_1 = v w^* in U(J~)`, `v_1 ~_h v`. Since `[v_1]_{K_1(B)} = 0`, exactness of
`K_0(B/J) -> K_1(J) -> K_1(B)` gives `[v_1]_{K_1(J)} = delta_0(g)` for some `g in K_0(B/J)`. `B/J` is
unital and properly infinite. By BRR Proposition 2.3(ii), both `g` and `-g` are classes of projections
in `B/J`, so pick `e in B/J` with `delta_0([e]) = [y']_{K_1(J)}`, `y' = exp(2 pi i h)`, `h = h^*` a lift of
`e`, arranging the sign so that `[y']_{K_1(J)} = [v_1]_{K_1(J)}`. This is the exponential map; see the
proof of Lemma 1 in `research/artifacts/lxi-halving-homotopy-and-extensions-2026-09-12.md`. Then
`y' in U(J~)` and `y' in U_0(B)` via `t -> exp(2 pi i t h)`. Put `v_J = v_1 y'^*`. Then
`v_J ~_h v_1 ~_h v` in `U(B)` and `[v_J]_{K_1(J)} = 0`. If `v_J in U_0(J~)`, then `v_J in U_0(B)` and so
`v in U_0(B)`, a contradiction. This is Rohde's Lemma 5.1.8, with weak K0-surjectivity replaced by
exponentials of projection lifts.

(b) `C = q_J^{-1}(q_J(sigma(T_2)))`, and the range of the \*-homomorphism `q_J ∘ sigma` is closed, so `C`
is a C\*-subalgebra. It contains `1` and `sigma(T_2)`, so it is properly infinite. `v_J in J~ subset C`,
and `[v_J]_{K_1(C)}` is the image of `[v_J]_{K_1(J~)} = 0`. Also `U_0(C) subset U_0(B)` and
`v_J notin U_0(B)`.

(c) If `z` is a central projection with `z ≠ 0, 1`, take `J_1 = Bz` and `J_2 = B(1-z)`. Then
`B = Bz (+) B(1-z)` and `U_0(B) = U_0(Bz) × U_0(B(1-z))`. Quotient-minimality gives `v(1-z) in
U_0(B(1-z))` and `vz in U_0(Bz)`, so `v in U_0(B)`, a contradiction. For the other two statements,
unitizations of stable ideals, and unitizations of stable rank one, are K1-injective. See the
extension-lemma node `k1-injectivity-extends-over-properly-infinite-quotients` and Rohde, Lemma 5.2.2.
Then (a) gives the contradiction. Square.

## 3. The non-prime case

**Theorem 3.** Let `(B, v)` be a quotient-minimal witness that is not prime. Take nonzero ideals
`J_1, J_2` with `J_1 ∩ J_2 = 0`, and put `B_i = B/J_i`, `D = B/(J_1 + J_2)`, with `pi_i: B_i -> D`.
Then `D ≠ 0`, `D` is properly infinite, and there are paths `g_i: [0,1] -> U(B_i)` from 1 to
`v_i = q_{J_i}(v)` such that the based loop `l = (pi_1 g_1) * (pi_2 g_2)̅` in `U(D)` satisfies both:
(i) `kappa_D(l) = 0` in `K_1(SD)`;
(ii) `[l] notin pi_{1*} pi_1(U(B_1), 1) · pi_{2*} pi_1(U(B_2), 1)`. In particular `l` is not
null-homotopic, so `l` is an undetected loop in `U(D)`.

*Proof.* Step 0 (`D ≠ 0`). If `J_1 + J_2 = B`, then by (F6) `B = B_1 (+) B_2`, and `J_1` is the range of a
central projection with `J_1 ≠ 0, B`. That contradicts Proposition 2(c). So `D` is a nonzero quotient of
`B`, hence properly infinite.

Step 1 (initial paths). By quotient-minimality `v_i in U_0(B_i)`. Choose paths `h_i` in `U(B_i)` from
1 to `v_i`. Since `[v] = 0` in `K_1(B)`, there is `n` and a path `Gamma` in `U(M_n(B))` from 1 to
`V = diag(v, 1_{n-1})`. Put `Gamma_i = q_{J_i} ∘ Gamma`, so that `pi_1 ∘ Gamma_1 = pi_2 ∘ Gamma_2 =
q_{J_1+J_2} ∘ Gamma =: Gamma_D`.

Step 2 (bookkeeping). Let `m_i = diag(h_i, 1) * Gamma_i̅`, a based loop in `U(M_n(B_i))`. In `U(M_n(D))`,
inserting the null backtrack `Gamma_D̅ * Gamma_D` (F3) gives
`diag(pi_1 h_1 * (pi_2 h_2)̅, 1) ≃ (diag(pi_1 h_1, 1) * Gamma_D̅) * (Gamma_D * diag(pi_2 h_2, 1)̅)
= (pi_1 ∘ m_1) * (pi_2 ∘ m_2)̅`. By (F3), for the loop `l_0 = pi_1 h_1 * (pi_2 h_2)̅`,
`kappa_D(l_0) = pi_{1*} kappa_{B_1}(m_1) - pi_{2*} kappa_{B_2}(m_2)`.

Step 3 (adjustment). By (F5) (or (F5')), applied to the properly infinite `B_i`, choose based loops `mu_i` in
`U(B_i)` with `kappa_{B_i}(mu_i) = - kappa_{B_i}(m_i)`. Put `g_i = mu_i * h_i`, still a path from 1 to
`v_i`. The new loops `m_i' = diag(g_i, 1) * Gamma_i̅ ≃ diag(mu_i, 1) * m_i` have
`kappa_{B_i}(m_i') = 0`. By Step 2 applied to `g_i`, the loop `l = pi_1 g_1 * (pi_2 g_2)̅` has
`kappa_D(l) = 0`. This proves (i).

Step 4 (reduction of (ii) to a lifting). Suppose `[l] = [pi_1 ∘ lambda_1] · [pi_2 ∘ lambda_2]^{-1}` for based
loops `lambda_i` in `U(B_i)`. Put `g_i' = lambda_i̅ * g_i`. Since the fundamental group of `U(D)` is
abelian (F3),
`[pi_1 g_1' * (pi_2 g_2')̅] = [pi_1 lambda_1]^{-1} [l] [pi_2 lambda_2] = 1`. So by (F3), `pi_1 g_1'` and
`pi_2 g_2'` are homotopic relative to endpoints. That is, there is a continuous `H: X = [0,1]^2 -> U(D)`
with `H(s,0) = pi_1 g_1'(s)`, `H(s,1) = pi_2 g_2'(s)`, `H(0,t) = 1` and `H(1,t) = d := q_{J_1+J_2}(v)`.

Step 5 (relative lifting). Let `Y = [0,1]×{0} ∪ {0}×[0,1] ∪ {1}×[0,1]`, and define `G_Y: Y -> U(B_1)` by
`G_Y(s,0) = g_1'(s)`, `G_Y(0,t) = 1`, `G_Y(1,t) = v_1`. It is continuous, since the pieces agree at the
two lower corners, and `pi_1 ∘ G_Y = H|_Y`. Radial projection from the point `(1/2, 2)` gives a
retraction `r: X -> Y`, and `rho_lambda(x) = (1 - lambda) x + lambda r(x)` is a homotopy in `X` from
`id` to `r` that fixes `Y` pointwise. Let
`P = {(f, g) in C(X, D) (+) C(Y, B_1) : f|_Y = pi_1 ∘ g}` and `Phi: C(X, B_1) -> P`,
`Phi(k) = (pi_1 ∘ k, k|_Y)`, a unital \*-homomorphism.

`Phi` is surjective. Given `(f, g) in P`, put `k_0 = g ∘ r`. Then `f - pi_1 ∘ k_0` vanishes on `Y`, so it
lies in `C_0(X \ Y, D)`. The \*-homomorphism `C_0(X \ Y, B_1) -> C_0(X \ Y, D)` induced by `pi_1` has closed
range containing the dense algebraic tensor product `C_0(X \ Y) ⊙ D`, so it is onto. Pick `k_1` in the
preimage, extend it by 0 on `Y`, and take `k = k_0 + k_1`.

The path `lambda -> W_lambda = (H ∘ rho_lambda, G_Y)` lies in `U(P)`, because `rho_lambda` fixes `Y`. It is
norm continuous by uniform continuity of `H`. `W_0 = (H, G_Y)` and
`W_1 = (H|_Y ∘ r, G_Y) = Phi(G_Y ∘ r)`. So `W_0 Phi(G_Y ∘ r)^* in U_0(P)`, and by (F1) it equals `Phi(K_0)`
for some `K_0 in U_0(C(X, B_1))`. Put `G = K_0 (G_Y ∘ r)`. Then `pi_1 ∘ G = H` and `G|_Y = G_Y`.

Step 6 (contradiction). `g_1''(s) = G(s, 1)` is a path in `U(B_1)` from `G_Y(0,1) = 1` to `G_Y(1,1) = v_1`,
with `pi_1 g_1'' = H(·, 1) = pi_2 g_2'`. By (F6), `(g_1'', g_2')` is a path in `U(B)` from 1 to `v`,
contradicting `v notin U_0(B)`. This proves (ii). Taking `lambda_i` constant shows `[l] ≠ 1`. Square.

**Corollary 4.** Under the hypotheses of Theorem 3, `(C(T, D), l)` is a witness. Here `l` is viewed as a
unitary of `C(T, D)` via `[0,1]/{0,1} = T`.

*Proof.* `C(T, D)` contains `D` as constants, so it is unital and properly infinite. The unital
\*-homomorphism `j: (SD)~ -> C(T, D)`, `x + lambda 1 -> x + lambda 1_D`, is injective (evaluate at
`t = 0`), and `j(l^) = l`. So `[l]_{K_1(C(T,D))} = j_*(kappa_D(l)) = 0`. If `l in U_0(C(T, D))`, then by (F4)
`l` is based null-homotopic, contradicting Theorem 3(ii). Square.

## 4. The reduction

Consider the following statements.
- (P) Every quotient-minimal witness `(B, v)` with `B` prime fails to exist; that is, `v in U_0(B)`
  whenever `B` is prime, properly infinite, `[v] = 0` and `v` is null modulo every nonzero ideal. This is
  implied by LXI for prime algebras.
- (L) For every unital properly infinite `D`, `kappa_D: pi_1(U(D), 1) -> K_1(SD)` is injective.

**Corollary 5.** LXI holds iff (P) and (L) hold.

*Proof.* If LXI holds, (P) is immediate. For (L), take a loop `l` with `kappa_D(l) = 0`. As in Corollary 4,
`l in U(C(T, D))` is K1-trivial in a properly infinite algebra, so LXI puts it in `U_0(C(T, D))`, and (F4)
makes it based null-homotopic.

Conversely, suppose (P) and (L) hold and `(A, u)` is a witness. Proposition 1 gives a quotient-minimal
witness `(B, v)`. By (P), `B` is not prime. Theorem 3 gives an undetected loop in `U(D)` for some nonzero
properly infinite `D`, contradicting (L). Square.

**Proposition 6.** For unital properly infinite `D`, (L) holds for `D` iff the map
`pi_1(U(D), 1) -> pi_1(U(M_2(D)), 1)`, `[l] -> [diag(l, 1)]`, is injective.

*Proof.* If `diag(l, 1)` is null, then `kappa_D(l) = kappa_D(diag(l,1)) = 0`, so (L) gives `l` null.
Conversely, let `kappa_D(l) = 0`. In `M_2(C(T, D))` the unitary `diag(l, 1)` is K1-trivial and commutes
with `p = diag(1, 0)`. Both `p` and `1 - p` are properly infinite and full, since they are equivalent to the
properly infinite unit of `C(T, D)` and generate `M_2`. By BRR Lemma 2.4(ii), `diag(l, 1) in
U_0(M_2(C(T, D)))`, and (F4) gives a based null-homotopy in `U(M_2(D))`. Injectivity then gives `l` null.
Square.

So (L) is the loop analogue of BRR Proposition 5.2(ii) (`U(A)/U_0(A) -> U_2(A)/U_0^2(A)` injective).

## 5. Remarks and limits

1. Neither (P) nor (L) is known to imply LXI by itself. The reduction is useful only if one of them
   turns out more tractable, or if a counterexample to (L) is easier to build than a general witness.
   `C(T, D)` is never prime, since `C(T)` is central, so Theorem 3 cannot be iterated to force primeness.
2. Under the halving hypothesis (c), every unital properly infinite algebra with `[1] = 0` is
   K1-injective (artifact `lxi-halving-homotopy-and-extensions-2026-09-12`, Theorem 2). Corollary 4 then
   forces `[1_D] ≠ 0` in `K_0(D)` for every pair `J_1, J_2` in Theorem 3, because
   `K_0(D) -> K_0(C(T, D))` is split injective and sends `[1_D]` to `[1]`. Applied to `B` itself and to
   the witnesses `C` of Proposition 2(b), (c) also forces `[1_B] ≠ 0` and `[1_C] ≠ 0`. By Blanchard
   (arXiv:0804.4624v13, Proposition 4.2 (i)<=>(v) and Remarks 4.7(i)), LXI fails iff the specific unitary
   `v` of his Proposition 4.6(iv) makes `(T_2 *_C T_2, v)` a witness. Suppose it does. Let `B` be a
   quotient-minimal quotient from Proposition 1, and let `J_0, J_1` be the ideals of `B` generated by the
   images of `1 - s_1 s_1^* - s_2 s_2^*` from the two copies of `T_2`. Under (c) both are nonzero, since
   otherwise `O_2` embeds unitally in `B`, so `[1_B] = 0`. If `J_0 ∩ J_1 = 0` in `B`, then
   `D = B/(J_0 + J_1)` is a nonzero quotient of `O_2 *_C O_2`, so `[1_D] = 0`, contradicting the first
   sentence. So under (c), `J_0 ∩ J_1 ≠ 0` in `B`.
3. Theorem 3 needs only that `B_1`, `B_2` realize all of `K_1(S B_i)` by based loops in `U(B_i)` (weak
   K0-surjectivity with `n = 1`), together with proper infiniteness of `D` for Corollary 4.
4. Separable witnesses suffice (BRR Theorem 5.5(vi) reduces to `O_inf * O_inf`), and their quotients are
   separable. So in (P) one may add "separable", and then prime is primitive (Dixmier; not rechecked).
   Whether `O_inf * O_inf` or its quotient-minimal quotient is prime was not determined.
5. Known cases.
   - (P) contains the statement that every simple unital properly infinite algebra is K1-injective, because
     the quotient condition is vacuous for simple `B`. That statement is known for purely infinite simple
     `B` (Cuntz; Rohde Theorem 3.1.3) and for Z-stable `B` (Jiang, graph node
     `z-stable-unital-algebras-are-k1-bijective`). Simple properly infinite algebras need not be purely
     infinite. M. Rordam, *A simple C\*-algebra with a finite and an infinite projection*, Acta Math. 191
     (2003), arXiv:math/0204339v2, Corollary 7.1 (read 2026-09-16), gives a nuclear unital separable
     simple infinite `A = p(D ⋊ Z)p` that is not purely infinite. Every simple infinite C\*-algebra is
     properly infinite, as stated in the proof of Corollary 7.2 there, following Cuntz.
   - (L) holds for `D` whenever `C(T, D)` is K1-injective, by the first half of the proof of Corollary 5.
     This covers Z-stable `D` and purely infinite simple `D`. The second case uses Rohde's Theorem 5.2.11:
     unital continuous `C(X)`-algebras over finite-dimensional `X` with purely infinite simple fibres are
     K1-injective. Its BRR inputs were not rechecked.

## 6. Sources consulted (2026-09-16)

- E. Blanchard, R. Rohde, M. Rordam, *Properly infinite C(X)-algebras and K1-injectivity*,
  arXiv:0704.1554v1 (12 Apr 2007): Proposition 2.3, Lemma 2.4, Proposition 5.2, Theorem 5.5 (read in
  full text).
- E. Blanchard, arXiv:0804.4624v13, Section 4 (Propositions 4.2 and 4.6, Remarks 4.7), read in full text.
- R. Rohde, *K1-injectivity of C\*-algebras*, PhD thesis, IMADA, University of Southern Denmark, March 2009
  (supervisor M. Rordam; PDF at https://web.math.ku.dk/~rordam/students/rohde-thesis.pdf), Theorem 3.1.3,
  Lemmas 5.1.6--5.1.9, 5.2.2 and 5.2.3, Proposition 5.2.9 and Theorem 5.2.11 (read in full text).
- C. Schafhauser, A. Tikuisis, S. White, arXiv:2506.10902v2 (2026-05-08): LXI still listed as open.
- A. Toms, arXiv:2609.09535 (2026-09-08) concerns Problem LIX, not LXI.
- Rordam--Larsen--Laustsen, CUP 2000, Chapter 11 (Bott periodicity) and Chapter 12 (exponential map),
  used as standard background. Theorem numbers were not rechecked. The one consequence Theorem 3 needs
  is reproved in (F5').
- M. Rordam, arXiv:math/0204339v2 (Acta Math. 191 (2003)): Proposition 2.1, Lemma 2.2 and Corollaries
  7.1--7.2, read 2026-09-16 (referee addition).
- Novelty hedge (referee): Theorem 3 was not found in BRR, Blanchard or Rohde. Its mechanism is a
  Mayer--Vietoris-type gluing along a pullback, which is standard in K-theory, so a version of it may exist
  elsewhere in the literature.
