# The state upgrade (U1): what a K_0 state on the anti-central summand does and does not determine

Lane `w4-upg-state` (family UPG), 2026-09-12. Target: step (U1) of
`ternary-anti-central-states-force-nontrivial-rank-models`. The question: does a state on
`(K_0(S_-), [eps_-])` give a Sylvester matrix rank function `N` on `S_- = eps_- F_3[G_3]` with
`N(eps_-) = 1`? Here `G_3 = L_(F_3)(1,2)^x`.

## 0. Summary

- **(U1) is exactly "rank condition implies a rank function" for `S_-`.**
  - The census (Theorem E) already shows that a state exists iff `S_-` satisfies the rank condition.
  - So (U1) asks whether the rank condition on `S_-` yields a Sylvester matrix rank function. No group
    input is involved in that implication.
- **Theorem A (established here).** The zero set of any Sylvester matrix rank function is a proper
  two-sided ideal, and the quotient is weakly finite with a faithful rank function.
  - **Consequence for `S_-`:** (U1) forces a nonzero weakly finite image of `S_-` into whose units `G_3`
    embeds with `z -> -1`.
  - **So (U1) splits in two:**
    - (U1a) a state gives a nonzero weakly finite image;
    - (U1b) such an image carries a rank function.
- **Proposition B (established here).** Any rank function extending a state `s` lies between an outer
  and an inner `s`-rank.
  - The two agree on von Neumann regular elements, so the extension is unique there.
  - They do not agree on nilpotents. On `F_3[C_3]` the state is unique, while rank functions give
    `rk(x-1)` every value in `[0, 2/3]`.
- **Where the content sits.** A state pins the ranks of all regular elements and nothing else. Every
  root element `x_12(1)` of `G_3` has order three, and `x_12(1) - 1` is not regular in `F_3[<x_12(1)>]`.
  So what (U1) must supply is a consistent choice of Jordan types for order-three unipotents. That is
  the data the rank gate studies: the root normal form `N = A - A^2` and the two-root identity.
- **Calibration.** The natural attempt at a ring with the rank condition and no rank function glues
  matrix algebras along a nilpotent. It collapses back to a `K_0` obstruction, because nilpotents in
  matrix algebras are regular (Section 3). A general counterexample to (U1) needs conflicts on
  non-regular elements.

## 1. Theorem A: rank functions factor through weakly finite quotients

Throughout, `A` is a unital ring and `N` a Sylvester matrix rank function on `A`, normalized by `N(1) = 1`.
The axioms are:
- `N(I_n) = n`;
- `N(XY) <= min(N(X), N(Y))`;
- `N(X ⊕ Y) = N(X) + N(Y)`;
- `N([[X, Z],[0, Y]]) >= N(X) + N(Y)`.

**Lemma A.1.** `N(I_m - BA) - m = N(I_n - AB) - n` for `A` of size `n x m` and `B` of size `m x n`.

*Proof.*
- `[[I_n, A],[B, I_m]] = [[I_n, 0],[B, I_m]] · [[I_n, A],[0, I_m - BA]]`.
- `[[I_n, A],[0, D]] = [[I_n, 0],[0, D]] · [[I_n, A],[0, I_m]]`, and the last factor is invertible.
- Multiplying by invertible matrices does not change `N`, since `N(XU) <= N(X) = N(XU U^(-1)) <= N(XU)`.
- So the rank of the block matrix is `n + N(I_m - BA)`.
- Symmetrically, `[[I_n, A],[B, I_m]] = [[I_n, A],[0, I_m]] · [[I_n - AB, 0],[B, I_m]]` and
  `[[D', 0],[B, I_m]] = [[D', 0],[0, I_m]] · [[I_n, 0],[B, I_m]]`, which gives `N(I_n - AB) + m`. ∎

**Theorem A.** `ker N = {x in A : N(x) = 0}` is a proper two-sided ideal, `N` descends to a faithful
Sylvester matrix rank function on `A / ker N`, and `A / ker N` is weakly finite: `AB = I_n` implies
`BA = I_n` there, for every `n`.

*Proof.*
1. **Ideal.** `x + y = [1 1] · diag(x, y) · [1 1]^T`, so `N(x + y) <= N(x) + N(y)`. Also `N(axb) <= N(x)`.
   The ideal is proper since `N(1) = 1`.
2. **Matrices with entries in the kernel.** A matrix has `N(X) = 0` iff all its entries lie in `ker N`.
   Each entry is `e_i^T X e_j`, so has rank at most `N(X)`. Conversely `X = sum E_ij x_ij` has rank at
   most `sum N(x_ij)`.
3. **Descent.** `N(X + K) <= N(X) + N(K) = N(X)` when `K` has kernel entries, and symmetrically. So `N`
   is well defined on the quotient, and it is faithful there by step 2.
4. **Weak finiteness.** If `AB = I_n + K` with kernel entries, then `N(I_n - AB) = 0`. By Lemma A.1 with
   `m = n`, `N(I_n - BA) = 0`, so `BA = I_n` modulo the kernel. ∎

**Corollary A.2 (the anti-central summand).** Suppose `N` is a Sylvester matrix rank function on `S_-`
with `N(eps_-) = 1`. Put `Q = S_- / ker N`. Then:
1. `Q` is a nonzero weakly finite `F_3`-algebra with a faithful rank function.
2. `g -> [g] eps_- + ker N` embeds `G_3` into `Q^x`, and sends `z` to `-1`.
3. Moreover `N((1 - [g]) eps_-) > 0` for every `g != 1`.

*Proof.*
1. By Theorem A.
2. **A rank function on the whole group algebra.** `X -> X eps_-` is a unital ring map
   `F_3[G_3] -> S_-`, since `eps_-` is a central idempotent. So `rk(X) = N(X eps_-)` is a Sylvester
   matrix rank function on `F_3[G_3]`.
3. **Its null subgroup is trivial.** By `simple-group-rank-functions-are-augmentation-or-detecting`,
   `N_rk = {g : rk(1 - [g]) = 0}` is a normal subgroup.
   - `rk(1 - [z]) = N(2 eps_-) = N(eps_-) = 1`, so `z` is not in `N_rk`.
   - A normal subgroup of `G_3` missing `z` meets `<z>` trivially.
   - Its image in `PG = G_3/<z>` is normal, hence `1` or `PG`, since `PG` is simple.
   - If the image is `PG`, then `G_3 = N_rk × <z>`, which is not perfect, a contradiction.
   - So `N_rk = 1`. The inputs are perfection of `G_3` (`leavitt-gl-equals-el-and-perfect-unit-group`)
     and simplicity of `PG` (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`), the same ones used in
     `ternary-leavitt-rank-models-move-z-iff-nontrivial`.
4. **Consequences.** `N_rk = 1` gives part 3. Faithfulness of the descended rank function then gives
   injectivity in part 2. ∎

**What this does to (U1).** A state on `(K_0(S_-), [eps_-])` is the same as the rank condition on `S_-`
(census Theorem E). So (U1) implies:

> **(U1a)** If `S_-` satisfies the rank condition, then `S_-` has a nonzero weakly finite image in which
> `G_3` embeds with `z -> -1`.

The rest of (U1) is:

> **(U1b)** Such an image, with a state, carries a Sylvester matrix rank function.

(U1a) holds trivially if `S_-` is itself stably finite, which is the anti-central half of Kaplansky's
direct finiteness for `G_3`. If `S_-` is not stably finite but still satisfies the rank condition, (U1a)
asks for a proper ideal whose quotient is weakly finite. That is Malcolmson's "weakly finite image"
problem for this ring; I have not read that source locally, so it is flagged as unverified.

## 2. Proposition B: states pin regular elements and leave nilpotents free

Let `s` be a state on `(K_0(A), [A])`. For a matrix `X` of size `m x n` define:
- the **inner s-rank** `rho_s(X) = inf s([P])` over f.g. projective `P` through which `X` factors,
  i.e. `X = U e V` with `e` an idempotent `k x k` matrix and `P = eA^k`;
- the **outer s-rank** `rho^s(X) = sup s([f])` over idempotent matrices `f = L X R`.

**Proposition B.**
1. `rho^s <= rho_s`.
2. Every Sylvester matrix rank function `N` with `N(e) = s([e])` on idempotent matrices satisfies
   `rho^s <= N <= rho_s`.
3. If `X` is von Neumann regular (`X = XYX` for some `Y`), then `rho^s(X) = rho_s(X) = s([XY])`. So every
   such extension `N` of `s` has `N(X) = s([XY])`, and on a von Neumann regular ring the extension, when
   it exists, is unique.
4. On `F_3[C_3] = F_3[x]/(x-1)^3` the state is unique (the only idempotents are `0` and `1`). Rank
   functions `N` realize every value `N(x - 1)` in `[0, 2/3]`, and no other values.

*Proof.*
1. If `f = L X R` and `X = U e V`, then `f = (LU) e (VR)`. So `fA^k` is a retract of `eA^(k')`, hence
   `[f] <= [e]` and `s(f) <= s(e)`.
2. `N(X) = N(U e V) <= N(e) = s(e)`, and `s(f) = N(f) = N(L X R) <= N(X)`.
3. `e = XY` is idempotent, `X = eX` factors through `eA^m`, and `e = I · X · Y`. So both bounds equal
   `s(e)`.
4. **The only state.** `K_0(F_3[C_3]) = Z`, with the unique state `s([F_3[C_3]]) = 1`.
   - **Realized values.** For `j = 1, 2, 3` let `N_j(X) = (1/j) rank` of `X` acting on
     `F_3[x]/(x-1)^j`. Each `N_j` is a Sylvester rank function, and `N_j(x - 1) = (j - 1)/j`, giving
     `0, 1/2, 2/3`. Convex combinations fill `[0, 2/3]`.
   - **Upper bound.** Put `u = x - 1`, so `u^3 = 0`.
     - Nullity (Frobenius with middle factor 1) gives `2N(u) <= 1 + N(u^2)`.
     - Frobenius with middle factor `u` gives `2N(u^2) <= N(u) + N(u^3) = N(u)`.
     - So `2N(u) - 1 <= N(u)/2`, which is `N(u) <= 2/3`.
   - **Bounds from s.** `rho^s(u) = 0` and `rho_s(u) = 1`. So the Sylvester axioms, not the state,
     produce the bound 2/3. ∎

**Consequence for `S_-`.** Every state on `(K_0(S_-), [eps_-])` is known to agree, on finite subgroups of
`E⋊V`, with the lifted trace `2·dim/|K|` (`anti-central-k0-states-equal-lifted-trace-on-signed-thompson`).
By part 3 that pins `N` on the regular elements of those finite-subgroup algebras, including every
semisimple one of order prime to three. By part 4 it pins nothing about the nilpotent part of
`F_3[<g>]` when `g` has order three. The root elements `x_ij(1)` of `G_3` have order three. So the ranks
`N(x_ij(1) - 1)` and `N((x_12(1) - 1)(x_23(1) - 1))`, which the rank gate studies, are exactly what a
state leaves undetermined. (U1) must produce them.
