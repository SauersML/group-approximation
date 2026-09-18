---
rg: 2
id: jacobson-mirror-exact-trace-part-multiplicative-proof
kind: route
title: Average over the mirror kernel, identify the invariant projection as central, and compute invariants of tensor products by Hilbert--Schmidt intertwiners
target: jacobson-mirror-exact-trace-part-is-multiplicative
requires:
  - jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
  - leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity
---

Notation as in the target. For a unitary representation `rho` of a group `K` on `H`, write `H^K` for the invariant
vectors and `p_K` for the projection onto them. For a finite group `F`, `avg_(y in F) rho(y) = p_F`.

## Step 0. The mirror kernel has no finite-dimensional unitary representations

**Lemma 0.** Let `V` be an infinite-dimensional `F_2`-vector space with a countable basis, and `L = GL_fin(V)`.
1. `L` is simple.
2. Every finite-dimensional unitary representation of `L` is trivial.

*Proof.*
1. Over `F_2` the determinant is trivial, so `L` is the increasing union of the groups `SL_k(F_2)` on the spans of
   the first `k` basis vectors. For `k >= 3` these are simple. A nontrivial normal subgroup `N` of `L` meets some
   `SL_k(F_2)` nontrivially, hence contains it, hence contains all later ones, so `N = L`.
2. Let `rho : L -> U(d)` be nontrivial. By 1 it is injective. For `k >= 1` the transvections
   `1 + e_1 (x) f`, with `f` in the span of `e_2^*, ..., e_(k+1)^*`, form a subgroup `(Z/2)^k` of `L`. Commuting
   unitary involutions are simultaneously diagonalizable with entries `+-1`, so an elementary abelian 2-subgroup of
   `U(d)` has order at most `2^d`. Take `k = d+1`: contradiction. QED.

The same holds for `L_+ ≅ L_- ≅ GL_fin(V_-)`.

## Step 1. The mirror-exact part (MX1)

Let `tau` be a trace of `P` with GNS triple `(pi, H, xi)`, and `M = pi(P)''`. Then
`<pi(g) xi, pi(h) xi> = tau(h^(-1) g)`, and the vector state of `xi` is a faithful normal trace on `M`.

- **The projections decrease.** `F_j <= F_(j+1)`, so the projections `p_j = p_(F_j) = avg_(y in F_j) pi(y)` decrease.
- **Their limit.** They converge strongly to the projection onto `bigcap_j H^(F_j) = H^(L_-)`, because
  `bigcup_j F_j = L_-`. Call it `z`. Any other chain with union `L_-` gives the same `z`.
- **Well-definedness.**
  `avg_(y in F_j) tau(y g) = <pi(g) xi, p_j xi> = <p_j pi(g) xi, xi> -> <z pi(g) xi, xi>`.
  So (MX1) exists and equals `<z pi(g) xi, xi>`.
  - The limit is intrinsic in the function `tau`. The same computation in any representation containing a vector
    `xi` with vector state `tau` gives the same value, since it is a limit of averages of `tau`.
- **`z` is central.**
  - `z` lies in `M`, as a strong limit of elements of `pi(L_-)`-span.
  - `L_-` is normal in `P`, so `pi(g) H^(L_-) = H^(L_-)` for every `g in P`, and `z` commutes with `pi(P)`.
  - So `z in M ∩ M' = Z(M)`.
- **Consequences.**
  - `tau^flat(g) = tau_M(z pi(g))`, with `tau_M` the trace on `M`. Since `z` is a central projection, this is
    positive definite and `P`-conjugation invariant.
  - For `y in L_-`, `z pi(y) = z`, so `tau^flat(g y) = tau^flat(g)`. So `tau^flat` factors through `P/L_- = E`.
  - `|tau^flat(g)| <= tau^flat(1) = m(tau) = tau_M(z)`.

**CE transfer.** Suppose `tau` is CE, so `M` embeds trace-preservingly in `R^omega`, and `m = m(tau) > 0`.
- Then the corner `zMz` with the trace `tau_M(.)/m` is also CE.
- `g -> z pi(g)` is a unitary representation of `E` into it, with trace `tau^flat/m`.
- So `tau^flat / m` is a CE character of `E`.

**Extremal dichotomy.** If `tau` is extremal, `M` is a factor, so the central projection `z` is `0` or `1`.
- If `z = 1`, then `pi(y) xi = xi` for all `y in L_-`. So `tau = 1` on `L_-`, and `tau^flat = tau`.
- If `z = 0`, then `tau^flat = 0`.
- Conversely, if `tau = 1` on `L_-`, then `||pi(y) xi - xi||^2 = 2 - 2 Re tau(y) = 0`, so `z != 0`.

For a general `tau`, take its extremal decomposition `tau = ∫ tau_x d mu(x)`. Then `avg_(F_j)` commutes with the
integral, and dominated convergence gives `tau^flat = ∫_({x : tau_x = 1 on L_-}) tau_x d mu(x)`. This is the
mirror-exact face.

## Step 2. The reduction (MX2)

**Forward.** Suppose `E` is hyperlinear.
- Then `delta_E` is CE, and so is its pullback `tau = delta_E o q` along `q : P -> E`: the GNS algebra is `L(E)`.
- `tau = 1` on `L_-`, so `tau^flat = tau`.
- On `L_+` this is `delta` restricted to `L_+ ≅ L`, which is nonconstant.

**Backward.** Suppose `tau` is CE and `tau^flat` is nonconstant on `L_+`.
- Then `m(tau) > 0`, because `|tau^flat| <= m(tau)`.
- `chi = tau^flat / m(tau)` is a CE character of `E` by Step 1.
- `chi(1) = 1`, and `chi(w_0) != 1` for some `w_0 in L \ {1}`.
- Theorem JH of `leavitt-corner-trace-gate-collapses-to-jacobson-hyperlinearity`, applied with `w = w_0`, gives:
  `E` is hyperlinear.

JH is stated for `E_n` acting on `F_2^(N x {1..n})` and `L_n = GL_fin`. That is `E_+` acting on `V_+^n`, with
`L_n = L`, so the theorem applies verbatim.

## Step 3. Invariants of tensor products (MX3)

**Proposition 3.** Let `K` be a group in which every finite-dimensional unitary representation is trivial. Let
`rho_1, rho_2` be unitary representations of `K` on `H_1, H_2`. Then

```text
(H_1 (x) H_2)^K = H_1^K (x) H_2^K.
```

*Proof.* The inclusion `⊇` is clear. For `⊆`, write `H_i = H_i^K (+) K_i`, with `K_i` invariant and `K_i^K = 0`.
Then `H_1 (x) H_2` splits into four invariant summands.
- **`H_1^K (x) K_2`.** As a representation it is a multiple of `K_2`. An invariant vector would expand in an
  orthonormal basis `(u_a)` of `H_1^K` as `sum u_a (x) v_a`, with each `v_a in K_2^K = 0`.
- **`K_1 (x) H_2^K`.** The same argument, with the roles exchanged.
- **`K_1 (x) K_2`.**
  - Identify it with the Hilbert--Schmidt operators `conj(K_1) -> K_2`, sending `u (x) v` to `conj(u') -> <u,u'> v`.
  - Under this identification the diagonal action becomes `T -> rho_2(k) T conj(rho_1)(k)^(-1)`.
  - So an invariant vector is a Hilbert--Schmidt intertwiner `T` from `conj(rho_1)` on `conj(K_1)` to `rho_2` on `K_2`.
  - If `T != 0`, then `T^* T` is a nonzero compact positive operator commuting with `conj(rho_1)(K)`. Its spectral
    projection for a nonzero eigenvalue is a finite-rank nonzero projection in the commutant.
  - Its range is then a nonzero finite-dimensional subrepresentation of `conj(K_1)`. By hypothesis it is trivial,
    so `conj(K_1)` has a nonzero invariant vector.
  - Complex conjugation then gives a nonzero invariant vector in `K_1`, a contradiction.
QED.

**Proof of (MX3).**
- Let `(pi_i, H_i, xi_i)` be GNS triples for `tau_i`. The function `tau_1 tau_2` is the vector state of
  `xi_1 (x) xi_2` in `pi_1 (x) pi_2`, so by Step 1 its flat part can be computed in `H_1 (x) H_2`.
- By Lemma 0, `K = L_-` satisfies the hypothesis of Proposition 3. So the projection onto `(H_1 (x) H_2)^(L_-)` is
  `z_1 (x) z_2`.
- Hence
  `(tau_1 tau_2)^flat(g) = <(z_1 (x) z_2)(pi_1(g) (x) pi_2(g))(xi_1 (x) xi_2), xi_1 (x) xi_2>
                         = tau_1^flat(g) tau_2^flat(g).`
QED.

## Step 4. The inert class N (MX4)

`tau in N` means `tau^flat(x) = m(tau)` for all `x in L_+`.
- If `m > 0`, this says the character `tau^flat/m` of `E` is `1` on `L`. By (JH1)(a) it then factors through
  `E/L = SL_n(A)`.

**4.1 Closure.**
- **Products.** If `tau_i^flat = m_i` on `L_+`, then by (MX3) `(tau_1 tau_2)^flat = m_1 m_2 = m(tau_1 tau_2)` on `L_+`.
  Tensor powers are the special case `tau_1 = tau_2`.
- **Mixtures.** `tau -> tau^flat` is affine and commutes with countable convex sums, by dominated convergence in
  (MX1). A convex combination of functions that are constant on `L_+` is constant on `L_+`. Direct sums of
  representations realize mixtures.
- **Conjugation.** `conj(tau)^flat = conj(tau^flat)`.
- **Automorphisms.** Let `alpha` be an automorphism of `P` with `alpha(L_-) = L_-` and `alpha(L_+) = L_+`. Then
  `(tau o alpha)^flat = tau^flat o alpha`, computed along the chain `alpha(F_j)`, and chain independence is Step 1.
  - Inner automorphisms qualify, because `L_+` and `L_-` are normal in `P`.

**4.2 Traces with no mirror-invariant vectors.** If `m(tau) = 0`, then `tau^flat = 0`, so `tau in N`.
- `delta_P`: in the regular representation of `P`, an `L_-`-invariant vector is constant on the infinite cosets of
  `L_-`, hence `0`.
- Extremal traces not identically `1` on `L_-`: Step 1, dichotomy.
- **The rank traces.** Take `psi_c(g) = 2^(-c rank(g-1))` on `GL_fin`, the fixed-point characters of (JH2), and let
  `tau_(a,b)` be `psi_a (x) psi_b` on the normal subgroup `L_+ x L_-`, extended by zero to `P`.
  - It is a trace: the extension by zero of a `P`-invariant positive definite function on a normal subgroup is
    positive definite, and conjugation preserves `rank(g-1)`.
  - For `b >= 1` and `g = (l_+, l_-)`,
    `avg_(y in F_j) tau_(a,b)(y g) = psi_a(l_+) avg_(y in F_j) psi_b(y l_-)`.
  - This tends to `0` by the estimate (5.2) below, applied after absorbing `l_-` into `F_j` for large `j`. Hence
    `m(tau_(a,b)) = 0`.
  - `tau_(a,b)(w) = 2^(-a)` and `tau_(a,b)(w') = 2^(-b)`. So for `a != b` these traces separate the head from the
    mirror head, which no restriction from `H_bi` does (`jacobson-mirror-head-swap-kills-ambient-approximations`).
  - Whether `tau_(a,b)` is CE is not decided here and is not needed.

**4.3 Ambient restrictions (list-free).** Let `G >= P` contain the group `Sigma` of finitary permutation matrices of
the basis `{e_s : s in Z x {1..n}}`, for instance `G = H_bi`, since `Sigma <= GL_fin(W)`. Let `sigma` be a trace of
`G`, with GNS triple `(pi,H,xi)`, and let `z` be the projection onto `H^(L_-)`.

Take `F_j = GL(span{e_s : s in S_j})` with `S_j = {-j,...,-1} x {1..n}`. Fix `x in L_+`, and choose a finite set
`S_x` of sites with `k >= 0` such that `x` preserves `span{e_s : s in S_x}` and fixes every other basis vector.
Fix `j`.

- **The permutation.** Choose `c_j in Sigma` that fixes `S_j` pointwise and maps `S_x` into negative sites outside
  `S_j`. For example, swap `S_x` with a block of sites `-k` with `k > j`.
- **`c_j` commutes with `F_j`.** For `y in F_j` and a site `s`:
  - If `s in S_j`, then `c_j y e_s = y e_s = y c_j e_s`, because `y e_s in span(S_j)` is fixed by `c_j`.
  - If `s notin S_j`, then `c_j e_s = e_(c_j s)` with `c_j s notin S_j`, which `y` fixes, and `y e_s = e_s`.
- **The transported element.** `x_j' = c_j x c_j^(-1)` is finitary and supported on `c_j(S_x)`, a set of negative
  sites. So `x_j' in L_-`.
- **The average.** By `G`-invariance of `sigma`,
  `avg_(y in F_j) sigma(y x) = avg_(y in F_j) sigma(c_j y x c_j^(-1)) = avg_(y in F_j) sigma(y x_j')`.
- **The estimate.** Write `p_j = avg_(y in F_j) pi(y)`. Because `x_j' in L_-`, we have `z pi(x_j') = z`, so
  ```text
  |avg_(F_j) sigma(y x_j') - m| = |<(p_j - z) pi(x_j') xi, xi>| = |<pi(x_j') xi, (p_j - z) xi>|
                                <= ||(p_j - z) xi|| -> 0.
  ```
- **Conclusion.** `(sigma|_P)^flat(x) = lim_j avg_(F_j) sigma(y x) = m(sigma|_P)`.

By Step 1 the flat part is intrinsic in the function, so `(sigma|_P)^flat` can be computed in the `G`-GNS space. Hence
`sigma|_P in N`.
- **Periodic finite models.** Their limit traces are traces of `H_bi` (limits of class functions of `H_bi` along an
  asymptotic homomorphism of `H_bi`), so they are covered.
- **No list needed.** This uses no classification of the characters of `GL(infinity,2)`.
- **Relation to the swap kill.** It strengthens the head-swap kill, which applies only when `sigma = 1` on `L_-`. Here
  `sigma` is arbitrary, and the conclusion holds on all of `L_+`.

**4.4 Consequence.** By 4.1–4.3, every trace of `P` obtained from `delta_P`, from the traces with `m = 0`, and from
restrictions of traces of `H_bi`, by finitely many products, countable mixtures, conjugations and `L_+`/`L_-`-
preserving automorphisms, lies in `N`. Its mirror-exact part is blind to the head.

## Step 5. The limit step (the survivor)

**5.1 Upper semicontinuity.** In any GNS space, `avg_(F_j) tau = <p_j xi, xi>` decreases in `j` to `m(tau)`. So
`m(tau) = inf_j avg_(F_j) tau` is an infimum of weak*-continuous functions, hence upper semicontinuous.
- For every `g` and `j`,
  `|tau^flat(g) - avg_(F_j) tau(y g)| = |<pi(g) xi, (p_j - z) xi>| <= (avg_(F_j) tau - m(tau))^(1/2)`.
- So if `avg_(F_j) tau -> m(tau)` uniformly over all traces `tau` of `P`, then `tau -> tau^flat` is a uniform limit
  of weak*-continuous maps, hence weak*-continuous. In that case `N` is weak*-closed.
- Without uniformity, a pointwise limit of traces in `N` can gain mirror-exact mass. This is the only operation of
  the standard toolkit that Steps 3–4 do not control.

**5.2 The estimate for the rank characters.** Let `F = GL_N(F_2)` and `k >= 1`.
- `avg_(F) psi_k = |{fixed points of y on (F_2^N)^k}|`, averaged over `y`, divided by `2^(kN)`. By Burnside's
  lemma this is the number of `F`-orbits on `N x k` matrices under left multiplication, divided by `2^(kN)`.
- The orbits correspond to the row spaces, which are the subspaces of `F_2^k` of dimension `r <= min(N,k)`.
- The Gaussian binomial satisfies `binom(k, r)_2 <= c_0 2^(r(k-r))`, with `c_0 = prod_(i >= 1) (1 - 2^(-i))^(-1) < 3.5`.
- The resulting exponent is `r(k-r) - kN = -(k(N-r) + r^2) <= -(N-r) - r^2`, because `k >= 1`.
- Hence
  ```text
  avg_(GL_N(F_2)) psi_k  <=  c_0 2^(-N) sum_(r >= 0) 2^(r - r^2)  <=  8 * 2^(-N),   uniformly in k >= 1.
  ```
- For `psi_infinity = delta`, the average is `1/|GL_N(F_2)|`.

**5.3 Conditional closure.** Suppose, as hypothesis (SK), that the extreme characters of `GL(infinity,2)` are
exactly `psi_k` for `k in {0,1,...,infinity}`.
- For a trace `tau` of `P`, the restriction `tau|_(L_-)` is a character of `L_-`. Decompose it as
  `sum_k c_k(tau) psi_k` (countable, by (SK)), with `c_k(tau) >= 0` summing to `1`.
- Chain independence lets us use `F_j = GL(span S_j) ≅ GL_(nj)(F_2)`.
- By 5.2, `0 <= avg_(F_j) tau - c_0(tau) <= 8 * 2^(-nj)` uniformly in `tau`, where `c_0(tau)` is the weight of
  `psi_0 = 1`.
- Letting `j -> infinity` gives `m(tau) = c_0(tau)`.
- So the convergence in 5.1 is uniform, `tau -> tau^flat` is weak*-continuous, and `N` is weak*-closed.

**Status of (SK).** (SK) is Skudlarek's classification. The graph imports only the countability of
`Ch(GL(infinity,q))`, from GKV (arXiv:1209.4945), which cites Thoma and Skudlarek for it. (SK) is therefore
**not imported**, and 5.3 is recorded as conditional.
- The target claims only 5.1 and 5.2 unconditionally.
- It does not claim closure of `N` under limits.

## Step 6. Calibration of the recorded next step

The entry "Mirror-head swap kills ambient approximations" on `agent-leavitt-not-bcs-negative-root-corner` asks for an
approximation of `P` that is not asymptotically `s`-invariant.
- **Wall-asymmetry is not sufficient.** Wall-asymmetric traces exist inside `N`, for example `tau_(a,b)` with `a != b`
  and `b >= 1` (Step 4.2).
- **Such traces are inert.** Every product `tau_1 tau_(a,b)` has flat part `0` (Steps 3 and 4.2), so it cannot be
  combined with the ambient traces of Step 4.3 into a head-seeing trace.
- **What is necessary.** By (MX2), a certificate must put CE mass on the mirror-exact face (traces equal to `1` on
  `L_-`) and charge the head there. That is equivalent to the hole.

So the recorded step (i) does not decompose the problem. The live positive mechanism is a limit that creates
mirror-exact mass (Step 5.1), and under (SK) that mechanism is closed as well. QED.
