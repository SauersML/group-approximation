# The Cohn elementary group EL_3(C_2): rank radical dichotomy, and what the two-root question asks

Lane `w4-cohn-el3` (families R4 and SUB), 2026-09-12. Target:
`cohn-coefficient-el3-rank-models-satisfy-two-root-identity`.

## 0. Summary

* **Section 1.** For any unital ring `S`, the two-root identity holds in every characteristic-two
  rank model of `EL_3(S)` exactly when every such model is trivial. The proof tensor-squares an
  identity-satisfying model.
* **Section 2.** Take `G = EL_3(C_2)`.
  * The kernel of `G -> EL_3(R)` is the simple finitary group `K = GL_fin(W x {1,2,3}, F_2)`.
  * The normal subgroups of `G` are `1`, `K` and `G`.
  * `C_2` embeds unitally in `R`, so `G <= R^x`.
  * So the rank radical of `G` is `1` or `G`. The value `K` is excluded.
* **Section 3.** Consequences.
  * The target is equivalent to: `G` has no nontrivial characteristic-two rank model, equivalently
    no injective one.
  * Chain: the Jacobson radical claim implies the target, which implies that `R^x` has no nontrivial
    characteristic-two rank model (the binary gate).
  * The target is not an intermediate lemma about completeness. It is the non-linear-soficity of
    one explicit subgroup `EL_3(C_2) <= R^x`.

Conventions. A *characteristic-two rank model* of a group `Gamma` is a homomorphism
`sigma : Gamma -> M^x`, where `M = prod_U M_(d_n)(F_n)` modulo rank-null sequences, every `F_n` has
characteristic two, and `rk` is the limit normalized rank. Write `n_ab(r) = sigma(x_ab(r)) - 1` and
`N_ab = n_ab(1)`. A model is *trivial* if its image is `{1}`.

## 1. Tensor squares turn "identity for all models" into "no nontrivial model"

**Proposition 1.1.** Let `S` be a unital ring and `sigma` a characteristic-two rank model of
`EL_3(S)` with `N_23 N_12 = 0`. Then `sigma (x) sigma` is a characteristic-two rank model of
`EL_3(S)`, and its root nilpotents `N'` satisfy

```text
rk(N'_23 N'_12) = 2 rk(N_12)^2 .
```

*Proof.*
1. **Tensor square is a model.** At level `n`, `g -> sigma_n(g) (x) sigma_n(g)` lies in
   `GL_(d_n^2)(F_n)`. Normalized rank is multiplicative on tensors, and
   `rk(AB (x) AB - C (x) C) <= 2 rk(AB - C)`, so the defects stay rank-null.
2. **Matrix units.** In characteristic two, `x_12(1)^2 = 1`, so `N_12^2 = 0` automatically.
   By `el3-unit-root-matrix-units-iff-two-root-identities`, `N_23 N_12 = 0` gives pairwise orthogonal
   idempotents `p_1, p_2, p_3` and `u_ij in p_i M p_j` with `sigma(x_ij(1)) = 1 + u_ij`,
   `u_ij u_jk = u_ik` and `u_ij u_ji = p_i`. So `rk(u_ij) = rk(p_i)`, and `u_12`, `u_21` make
   `rk(p_1) = rk(p_2) = rk(N_12)`.
3. **The product.** `N'_ab = u_ab (x) 1 + 1 (x) u_ab + u_ab (x) u_ab`. Every term of `N'_23 N'_12`
   containing `u_23 u_12 in p_2 M p_3 . p_1 M p_2 = 0` vanishes, so

   ```text
   N'_23 N'_12 = u_23 (x) u_12 + u_12 (x) u_23 .
   ```

4. **Ranks add.** The two summands have orthogonal left supports `p_2 (x) p_1` and `p_1 (x) p_2`,
   and orthogonal right supports `p_3 (x) p_2` and `p_2 (x) p_3`. So the sum is block diagonal, and
   its rank is `rk(u_23) rk(u_12) + rk(u_12) rk(u_23) = 2 rk(N_12)^2`. QED

**Corollary 1.2.** For a unital ring `S`, the following are equivalent:
- (a) every characteristic-two rank model of `EL_3(S)` satisfies `N_23 N_12 = 0`;
- (b) every characteristic-two rank model of `EL_3(S)` is trivial.

*Proof.* (b) gives (a). Assume (a) and let `sigma` be any model. By (a) and Proposition 1.1,
`2 rk(N_12)^2 = 0`, so `sigma(x_12(1)) = 1`. The element `x_12(1)` normally generates `EL_3(S)`:
Weyl conjugates give every `x_ab(1)`, and `[x_ac(1), x_cb(r)] = x_ab(r)`. So `sigma` is trivial.
QED

**Relation to the natural tensor square.** `rank-modelled-coefficients-violate-two-root-identities`
tensor-squares the *natural* model of a ring that has a unital rank model. Proposition 1.1
tensor-squares an *arbitrary* identity-satisfying model, so it also covers rings with no rank model:
`R`, `C_2` and `J`. Over each algebra it covers, `rank-models-of-el3-satisfy-the-two-root-identities`
is the same statement as the absence of nontrivial characteristic-two rank models of `EL_3`.

## 2. The structure of `G = EL_3(C_2)`

**Notation.**
- `C_2 = F_2<s_0, s_1, t_0, t_1 | t_i s_j = delta_ij>`, with normal-form basis `s_mu t_nu`
  (`mu, nu` in `W = {0,1}^*`).
- `q = 1 - s_0 t_0 - s_1 t_1`, and `R = L_(F_2)(1,2) = C_2/(q)`.
- `J = F_2<S, T | TS = 1>`.
- `pi : G -> EL_3(R)`.
- *Toeplitz representation:* `s_i delta_w = delta_(iw)`, `t_i delta_(iw) = delta_w`,
  `t_i delta_(jw) = 0` for `j != i`, and `t_i delta_empty = 0`, on `F_2[W]`. It is faithful, because
  `s_mu t_nu` maps `delta_(nu w)` to `delta_(mu w)` and kills the other basis vectors, and these
  partial maps are linearly independent.

**Lemma 2.1 (embeddings).** There are unital embeddings `J -> C_2 -> L_(F_2)(1,3) -> R`. So
`EL_3(J) <= G <= EL_3(R)`, and `EL_3(R) = GL_3(R) ~ R^x` is simple.
*Proof.*
1. **`J -> C_2`.** `S -> s_0`, `T -> t_0` sends the basis `S^i T^j` to basis words `s_0^i t_0^j`.
2. **`C_2 -> L(1,3)`.** Send `s_i, t_i` to the first two edge pairs. The Leavitt path algebra basis
   `mu nu*` excludes only pairs whose last edges are both the special edge `e_2`. Words over
   `{0,1}` never end in `e_2`, so the image of the normal-form basis is linearly independent.
3. **`L(1,3) -> R`.** `s_0 -> s_0`, `s_1 -> s_1 s_0`, `s_2 -> s_1 s_1`, and dually for `t`. The
   relations hold, and `L(1,3)` is simple, so the map is injective.
4. **The unit groups.** `GL_3(R) = EL_3(R)` by `leavitt-gl-equals-el-and-perfect-unit-group`. The
   module isomorphism `R ~ R^3` gives `M_3(R) ~ R`, hence `GL_3(R) ~ R^x`, and `R^x` is simple by
   `binary-leavitt-unit-group-is-simple`. QED

**Lemma 2.2 (finitary kernel).** `ker pi = K := GL_fin(W x {1,2,3}, F_2)`, the finitary invertible
operators on `F_2[W]^3` in the basis `delta_w e_a`. `K` is infinite and simple, and `C_G(K) = 1`.
*Proof.*
1. **`ker pi <= K`.** The ideal `(q)` is spanned by `s_mu q t_nu`, which is the matrix unit
   `delta_nu -> delta_mu`, so `(q)` is the finitary operators. So
   `ker pi = G ∩ (1 + M_3((q))) <= K`.
2. **`K <= G`.** Over `F_2`, `K = SL_fin` is generated by the transvections `1 + E_(x,y)` with
   `x != y`. For `x = (a, mu)` and `y = (b, nu)` with `a != b`, `1 + E_(x,y) = x_ab(s_mu q t_nu)`. For
   `a = b` and `mu != nu`, pick `c != a` and use
   `[1 + E_((a,mu),(c,lambda)), 1 + E_((c,lambda),(a,nu))] = 1 + E_((a,mu),(a,nu))`.
3. **Simple.** `K` is the finitary special linear group of an infinite-dimensional space, which is
   simple.
4. **Trivial centralizer.** An operator commuting with every `E_(x,y)` is scalar, so over `F_2` it
   is `1`. `G` acts faithfully on `F_2[W]^3`, so `C_G(K) = 1`. QED

**Lemma 2.3 (normal subgroups).** A normal subgroup `N` of `G` is `1`, `K` or `G`.
*Proof.* `N ∩ K` is normal in `K`, so it is `1` or `K`.
- If `N ∩ K = 1`, then `[N, K] <= N ∩ K = 1`, so `N <= C_G(K) = 1`.
- If `N >= K`, then `N/K` is normal in the simple group `EL_3(R)`. QED

**Theorem 2.4 (rank radical dichotomy).** Let `Rad(G)` be the intersection of the kernels of all
characteristic-two rank models of `G`. Then `Rad(G)` is `1` or `G`. So `G` has a nontrivial
characteristic-two rank model iff it has an injective one.
*Proof.* `Rad(G)` is normal, so by Lemma 2.3 it suffices to exclude `Rad(G) = K`.
1. Suppose `Rad(G) = K`. Some model `sigma` is nontrivial and kills `K`, so `sigma = tau o pi` for a
   nontrivial model `tau` of `EL_3(R)`.
2. `EL_3(R)` is simple, so `tau` is injective.
3. With `iota : G -> EL_3(R)` the embedding of Lemma 2.1, `tau o iota` is an injective model of `G`.
   So `Rad(G) = 1`, a contradiction.
4. For the second sentence, use Lemma 2.3 again: a model with kernel `1` is injective, and one with
   kernel `K` yields an injective model through `iota` as in step 3. QED

## 3. What the target asks, and where completeness sits

**Corollary 3.1.** The following are equivalent:
1. `cohn-coefficient-el3-rank-models-satisfy-two-root-identity`;
2. every characteristic-two rank model of `EL_3(C_2)` is trivial;
3. `EL_3(C_2)` has no injective characteristic-two rank model.

*Proof.* (1) iff (2) is Corollary 1.2 with `S = C_2`. (2) iff (3) is Theorem 2.4. QED

**Corollary 3.2 (chain).**

```text
binary-jacobson-el3-rank-radical-is-the-finitary-kernel
  ==>  cohn-coefficient-el3-rank-models-satisfy-two-root-identity
  ==>  R^x has no nontrivial characteristic-two rank model.
```

*Proof.*
1. **First arrow.** Suppose every model of `EL_3(J)` kills the head `x_13(Q)`, `Q = 1 - ST`. Its
   image `x_13(1 - s_0 t_0)` in `G` is nontrivial. If `Rad(G) = 1`, some model of `G` retains it, and
   restricting to `EL_3(J)` retains the head, a contradiction. So `Rad(G) = G` by Theorem 2.4.
2. **Second arrow.** A nontrivial model of `R^x ~ EL_3(R)` is injective by simplicity, so it
   restricts to an injective model of `G <= EL_3(R)`, against (3) of Corollary 3.1. This is the
   subgroup form of the node's pullback remark. QED

**Reading.**
- **What the target is.** The Cohn-coefficient identity is not a lemma about which ring relations
  enter a proof. It is the non-linear-soficity, in characteristic two, of the explicit finitely
  generated group `EL_3(C_2)`, sitting between `EL_3(J)` and `R^x`. Neither arrow of Corollary 3.2
  is known to reverse.
- **Monotonicity.** Non-linear-soficity passes up to supergroups. So the three statements are
  ordered by the subgroup chain `EL_3(J) <= EL_3(C_2) <= R^x`.
- **Where completeness is load-bearing.** A triviality proof for `R^x` can avoid the completeness
  relation only by proving triviality for a subgroup whose coefficient ring lacks it, such as
  `EL_3(C_2)` or `EL_3(J)`, whose rank radicals are `1` or maximal. So completeness is load-bearing
  exactly when `EL_3(C_2)` is characteristic-two linear sofic.
- **Two differences from the Jacobson case.** For `J` the quotient `EL_3(F_2[z, z^-1])` is
  residually finite, so models exist and the radical question is `1` versus `L`. For `C_2` the
  quotient is the simple group `R^x`, so the question is `1` versus everything, and every model
  construction must represent the finitary kernel faithfully.
