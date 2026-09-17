# Direct limits add no slack to spectral DT certificates (2026-09-17)

Worker: swarm-0917-w5-bs-price-one-non-ah. Target cone:
`fpbs-residual-price-one-non-ah-class-nonuniqueness`, toward
`fpbs-benjamini-schramm-universal`.

**Motivation.** Wave 4 stopped at single torsion groups (Tarski monsters,
`B(m,n)`), where every relative-threshold route dies. The standard handle on
these groups is that they are direct limits of hyperbolic groups
(`free-burnside-is-a-limit-of-hyperbolic-groups`). The hyperbolic approximants
all have strict gaps (`fpbs-hyperbolic-nonunimodular-critical-l2-gap`). This
artifact answers exactly what such approximant information can give for the
limit.

## 0. Setting and notation

* `D` is a finite label set. A marked group `(G, D)` is a group with a map
  `D -> G` whose image generates.
* `Cay(G, D)` is the simple graph with edges `{x, xs}` for `s` in the image of
  `D union D^{-1}` with `s != e`. `B_R(G)` is the word ball, and `o = e`.
* A **surjective chain with limit `Gamma`** consists of:
  * marked groups `(H_i, D)` for `i >= 0`;
  * label-preserving surjections `phi_i : H_i -> H_{i+1}` and
    `psi_i : H_i -> Gamma`, with `psi_{i+1} phi_i = psi_i`;
  * the condition `ker psi_0 = union_j ker(H_0 -> H_j)`.
* For a group `G` and finitely supported `f : G -> [0, infinity)`, write
  `lambda_G(f) = sum_g f(g) lambda_g` on `l2(G)`.
  * `f*(g) = f(g^{-1})` and `(f*h)(g) = sum_x f(x) h(x^{-1} g)`, so
    `lambda(f) lambda(h) = lambda(f*h)` and `lambda(f)^* = lambda(f*)`.
  * `sp_G(f)` is the spectral radius of `lambda_G(f)`.
* For a homomorphism `phi : H -> G`, put `(phi_* f)(g) = sum_{phi x = g} f(x)`.
  It is a `*`-homomorphism for convolution on finitely supported functions.
* The DT boundary measure `nu^G_{S,p}` is as in
  `fpbs-spectral-dt-certificate-bounds-connectivity-operator`.
  * `p_S(G) = sup{p : sp_G(nu^G_{S,p}) < 1}`.
  * `p_sDT(G) = sup_S p_S(G)`.

## 1. Injectivity radius

**Lemma 1.1.** For every `R` there is `i(R)` such that for all `i >= i(R)`:

* `ker psi_i ∩ B_{2R+4}(H_i) = {e}`;
* hence `psi_i` maps the labelled induced subgraph on `B_{R+1}(H_i)` isomorphically
  onto the one on `B_{R+1}(Gamma)`, rooted at `e`;
* and `phi_i` maps `B_{R+1}(H_i)` isomorphically onto `B_{R+1}(H_{i+1})`.

In particular `(H_i, D) -> (Gamma, D)` locally.

*Proof.*

1. `B_{2R+4}(H_0)` is finite, so `W = ker psi_0 ∩ B_{2R+4}(H_0)` is finite.
2. By the direct-limit condition, each `w` in `W` dies in some `H_{j(w)}`. Put
   `i(R) = max_w j(w)`.
3. Let `i >= i(R)` and take `x` in `ker psi_i ∩ B_{2R+4}(H_i)`.
   * `H_0 -> H_i` is label preserving, so `x` is the image of some `w` in
     `B_{2R+4}(H_0)`.
   * `psi_0(w) = psi_i(x) = e`, so `w` is in `W` and dies in `H_i`. Hence
     `x = e`.
4. Now take `x, y` in `B_{R+1}(H_i)`.
   * If `psi_i x = psi_i y`, then `x^{-1} y` lies in `ker psi_i ∩ B_{2R+4}`, so
     `x = y`.
   * If `psi_i y = psi_i(x) psi_i(s)` for a label `s`, then `(xs)^{-1} y` lies
     in `ker psi_i` and has length at most `2R+3`, so `xs = y`. Likewise a label
     that is trivial in `Gamma` is trivial in `H_i`.
   * Surjectivity on balls is clear from the labels. So `psi_i` is a labelled
     ball isomorphism.
5. `phi_i` is injective on `B_{R+1}(H_i)` because `psi_i = psi_{i+1} phi_i` is,
   and it is surjective on balls. QED

**Covering.** Let `i_0 = i(1)`. For `i >= i_0`, the maps `psi_i` and `phi_i` are
bijective on each vertex neighbourhood. So they are covering maps of simple
graphs. From now on assume `i >= i_0`.

## 2. Thresholds increase along the chain

**Lemma 2.1 (covering coupling).** Let `pi : X -> Y` be a covering map of
connected, locally finite simple graphs with `pi(o~) = o`. For every `p` there
is a coupling of Bernoulli(`p`) bond percolation `omega^X` on `X` and `omega^Y`
on `Y` with `|K^X(o~)| >= |K^Y(o)|`. Hence `theta_X(p) >= theta_Y(p)` and
`p_c(X) <= p_c(Y)`.

*Proof.*

1. **Exploration.** Fix an enumeration of `E(Y)`. Explore `K^Y(o)` as follows.
   * Keep the explored vertex set `V_t`, starting at `V_0 = {o}`, and the set of
     examined edges.
   * At step `t`, examine the lowest-index unexamined edge with at least one
     endpoint in `V_t`.
   * If it is open and has an endpoint outside `V_t`, add that endpoint.
   * Every edge meeting the final cluster is examined at some finite step, since
     only finitely many edges have lower index. So `V_infinity = K^Y(o)`.
2. **Lifted tree.** Maintain a set `T_t` in `X` with `o~` in `T_0`, such that
   `pi` restricted to `T_t` is a bijection onto `V_t`.
   * Suppose step `t` examines `{u, v}` with `u` in `V_t` and `v` not in `V_t`.
   * Let `u~` be the lift of `u` in `T_t`, and `{u~, v~}` the unique lift of the
     edge at `u~`.
   * Declare `omega^X({u~, v~}) := omega^Y({u, v})`. If that coin is open, add
     `v~` to `T_t`.
   * `v~` is not in `T_t`, since `pi(T_t) = V_t` does not contain `v`.
   * The lifted edges used at different steps are distinct, because their images
     are distinct edges of `Y`.
   * All other edges of `X` receive independent Bernoulli(`p`) coins.
3. **Law.** The lifted edge at step `t` is a function of the coins already
   revealed, and is not among the previously used lifts. Given the past, its
   coin is Bernoulli(`p`) and independent. So `omega^X` is Bernoulli(`p`)
   percolation (adaptive revealing).
4. **Conclusion.** `T_infinity` is connected through open `X`-edges and
   `|T_infinity| = |K^Y(o)|`. So `|K^X(o~)| >= |K^Y(o)|`. QED

**Proposition 2.2.** For a surjective chain with limit `Gamma`, and
`i_0 <= i <= j`,

`p_c(H_i) <= p_c(H_j) <= p_c(Gamma)` and `p_c(H_i) -> p_c(Gamma)`.

*Proof.*

1. `psi_i` and `phi_i` are covering maps (Section 1). Lemma 2.1 gives the
   inequalities.
2. The chain converges locally (Lemma 1.1), and all graphs are infinite and
   transitive. Lemma 1.1 of `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`
   (node `fpbs-l2-gap-class-closed-under-local-limits`, Part 2) says: "If
   `G_k -> G` locally and all graphs are infinite, locally finite and
   transitive, then `liminf_k p_c(G_k) >= p_c(G)`."
3. Together, `p_c(H_i)` increases to `p_c(Gamma)`. QED

**Remark (direction).** Lemma 2.1 transfers lower bounds on cluster sizes from
a quotient to its covers. The approximants `H_i` are covers of `Gamma`. So the
coupling moves only `p_c`, the "easy" half of a gap, and it says nothing about
`p_u`: the lamplighter chain of Section 5 has `p_u(H_i) >= p_(2->2)(H_i) > p_c(H_i)`
on every approximant, while the limit has `p_c = p_u`. The next sections show
exactly what does transfer.

## 3. Norms of positive elements along the chain

**Lemma 3.1 (trace formula).** Let `a >= 0` be finitely supported on `G` with
`a = a*`, and suppose `lambda_G(a)` is a positive operator. Then

`||lambda_G(a)|| = sup_m a^{*m}(e)^{1/m} = lim_m a^{*m}(e)^{1/m}`.

*Proof.*

1. `a^{*m}(e) = <lambda(a)^m delta_e, delta_e> = ∫ t^m dmu(t)`, where `mu` is the
   spectral measure of `lambda(a)` at `delta_e`. It is a probability measure on
   `[0, ||lambda(a)||]`.
2. For a probability measure, `m -> (∫ t^m dmu)^{1/m}` is nondecreasing
   (Lyapunov). It is bounded by `||lambda(a)||`.
3. The trace `tau(x) = <x delta_e, delta_e>` is faithful on the group von
   Neumann algebra. If `tau(x^* x) = ||x delta_e||^2 = 0`, then
   `x delta_g = x rho_g delta_e = rho_g x delta_e = 0` for all `g`, where `rho`
   is the right regular representation. So `x = 0`.
4. For `s < ||lambda(a)||`, the spectral projection `E = 1_{(s,infinity)}(lambda(a))`
   is nonzero. So `mu((s, infinity)) = tau(E) > 0`, and
   `(∫ t^m dmu)^{1/m} >= s mu((s,infinity))^{1/m} -> s`. QED

**Lemma 3.2 (Kesten monotonicity).** Let `phi : H -> G` be a surjection and
`h >= 0` finitely supported on `H`. Then
`||lambda_H(h)|| <= ||lambda_G(phi_* h)||`.

*Proof.*

1. `||lambda(h)||^2 = ||lambda(h* * h)||`. Put `a_H = h* * h` and
   `a_G = (phi_* h)* * (phi_* h) = phi_*(a_H)`. Both satisfy Lemma 3.1.
2. `a_H^{*m} >= 0`. For `b >= 0`, `(phi_* b)(e) = sum_{x in ker phi} b(x) >= b(e)`.
3. So `a_H^{*m}(e) <= phi_*(a_H^{*m})(e) = a_G^{*m}(e)`. Take `m`-th roots and
   the supremum over `m` (Lemma 3.1). QED

**Pullback notation.** If `f >= 0` on `Gamma` is supported in `B_R(Gamma)` and
`i >= i(R)`, let `f_i` be `f ∘ psi_i` on `B_R(H_i)`, extended by `0`. By
Lemma 1.1:

* `psi_{i*} f_i = f`;
* `phi_{i*} f_i = f_{i+1}`.

**Proposition 3.3 (monotone convergence of norms).** For `f` as above,
`i -> ||lambda_{H_i}(f_i)||` is nondecreasing for `i >= i(R)`, and it converges
to `||lambda_Gamma(f)||`.

*Proof.*

1. **Monotone and bounded.** Lemma 3.2 with `phi_i` gives monotonicity. With
   `psi_i` it gives the bound by `||lambda_Gamma(f)||`.
2. **Convergence.** Put `a = f* * f` and `a_i = f_i* * f_i`. Fix `m`, and take
   `i >= i(mR)`.
   * `a_i^{*m}(e)` is the sum over tuples `(y_1, ..., y_{2m})` in `B_R(H_i)^{2m}`
     with `y_1^{-1} y_2 y_3^{-1} y_4 ... y_{2m} = e` of `prod_j f_i(y_j)`.
     Similarly for `a^{*m}(e)` over `B_R(Gamma)`.
   * `psi_i` is a bijection `B_R(H_i) -> B_R(Gamma)` and preserves the weights.
   * The alternating product has length at most `2mR`, and `ker psi_i` is
     trivial on `B_{2mR}(H_i)`. So the product is `e` in `H_i` iff its image is
     `e` in `Gamma`.
   * Hence `a_i^{*m}(e) = a^{*m}(e)`.
3. **Limit.** By Lemma 3.1,
   `lim_i ||lambda_{H_i}(f_i)||^2 >= a^{*m}(e)^{1/m}` for every `m`. The
   supremum over `m` is `||lambda_Gamma(f)||^2`. QED

At `f = |D|^{-1} 1_D` this recovers `rho(H_i) -> rho(Gamma)`, nondecreasing.

## 4. Certificates on the limit are exactly the uniform approximant certificates

**Lemma 4.1 (DT measures are ball-local).** Let `S` be a finite set in
`B_r(Gamma)` containing `e`, and let `i >= i(r+1)`. Put
`S_i = psi_i^{-1}(S) ∩ B_r(H_i)`. Then for every `p`,
`nu^{H_i}_{S_i,p} = (nu^Gamma_{S,p})_i`.

*Proof.* `nu_{S,p}(g) = p sum_{{u,v} in Delta S, v = g} P_p(o <->_S u)`
depends only on two things:

* the induced subgraph on `S`, which determines the connection probabilities
  inside `S`;
* the edges from `S` to `B_{r+1}`.

By Lemma 1.1, `psi_i` is a rooted labelled isomorphism of `B_{r+1}` that
carries `S_i` to `S`. QED

**Theorem 4.2 (no slack).** Let `(H_i, D)` be a surjective chain with limit
`Gamma`. Fix a finite `S` containing `e` and a parameter `p`. Write
`nu = nu^Gamma_{S,p}` and `nu_i = nu^{H_i}_{S_i,p}`.

1. **Restriction.** `sp_{H_i}(nu_i)` is nondecreasing in `i` and at most
   `sp_Gamma(nu)`. So `p_S(H_i) >= p_S(H_{i+1}) >= p_S(Gamma)`. Any certificate
   on `Gamma` is a certificate on every approximant, with the same `(S, p)`.
2. **Equivalence.** The following are equivalent:
   * (a) `sp_Gamma(nu) < 1`;
   * (b) there are `n >= 1` and `c < 1` such that
     `||lambda_{H_i}(nu_i^{*n})|| <= c` for all large `i`;
   * (b2) the same holds for infinitely many `i`.
3. **Threshold form.** `p_c(Gamma) < p_sDT(Gamma)` iff there are `S`,
   `p > p_c(Gamma)`, `n` and `c < 1` satisfying (b2). Every such certificate
   sits at margin at least `p - p_c(Gamma) > 0` above every `p_c(H_i)`
   (Proposition 2.2).

*Proof.* Let `S` lie in `B_r`, and put `R = r + 1`, so `nu` is supported in
`B_R`.

1. **Powers.**
   * `phi_{i*}` and `psi_{i*}` are convolution homomorphisms. So
     `phi_{i*}(nu_i^{*n}) = nu_{i+1}^{*n}` and `psi_{i*}(nu_i^{*n}) = nu^{*n}`.
   * `nu^{*n}` is supported in `B_{nR}`. For `i >= i(nR)`, the same bijection
     argument as in Proposition 3.3 gives `nu_i^{*n} = (nu^{*n})_i`.
2. **Part 1.** By Lemma 3.2,
   `||lambda_{H_i}(nu_i^{*n})|| <= ||lambda_{H_{i+1}}(nu_{i+1}^{*n})|| <= ||lambda_Gamma(nu^{*n})||`.
   Take `n`-th roots and let `n -> infinity`, using Gelfand's formula.
3. **(a) implies (b).** Gelfand's formula `sp = inf_n ||x^n||^{1/n}` gives `n`
   with `c := ||lambda_Gamma(nu^{*n})|| < 1`. Part 1 then bounds the
   approximants by `c`.
4. **(b2) implies (a).** By Proposition 3.3 applied to `f = nu^{*n}`, and by
   step 1, `||lambda_Gamma(nu^{*n})|| = lim_i ||lambda_{H_i}(nu_i^{*n})||`. The
   limit of a monotone sequence is its limit along any subsequence, so it is at
   most `c`. Hence `sp_Gamma(nu) <= c^{1/n} < 1`.
5. **Part 3.** Part 3 is part 2 together with Lemma 4.1 and Proposition 2.2. QED

**What is not claimed.** Part 1 gives `lim_i p_S(H_i) >= p_S(Gamma)`.

* Equality holds whenever `nu` is symmetric, since then `sp = ||.||` and
  Proposition 3.3 applies.
* For non-symmetric DT measures, a strict inequality would be one more way the
  inf over `n` and the sup over `i` fail to commute. This artifact does not
  decide it.
* Theorem 4.2 is stated so that it needs no such commutation.

## 5. Calibration: strict gaps on every hyperbolic approximant, none in the limit

**The chain.** Let `D = {a, t}`, and put

`H_i = < a, t | a^2, [a, t^{-k} a t^k] for 1 <= k <= i >`

and `L = < a, t | a^2, [a, t^{-k} a t^k] for k >= 1 >`.

`L` is the lamplighter group `Z/2 wr Z`. This is its standard presentation: all
conjugates `t^{-j} a t^j` have order 2 and commute pairwise, and conjugating by
`t^j` reduces `[a_j, a_l]` to `[a, a_{l-j}]`. The identity maps on labels give
a surjective chain with limit `L`: the relator sets increase and their union is
that of `L`.

**Proposition 5.1.** Each `H_i` is virtually free and not virtually cyclic.
Hence `Cay(H_i, D)` is a nonamenable Gromov hyperbolic Cayley graph.

*Proof.*

1. Let `A = (Z/2)^{i+1}` with basis `a_0, ..., a_i`. Let `C = <a_0, ..., a_{i-1}>`
   and `C' = <a_1, ..., a_i>`, both of index 2, with the isomorphism
   `theta : a_j -> a_{j+1}`.
2. The HNN extension `A *_theta` has presentation
   `< a_0..a_i, t | a_j^2, [a_j, a_l], t^{-1} a_j t = a_{j+1} for j < i >`.
3. Eliminate `a_j = t^{-j} a_0 t^j` by Tietze moves. The relation `a_j^2 = 1`
   follows from `a_0^2 = 1`. The relation `[a_j, a_l]` is conjugate to
   `[a_0, a_{l-j}]`. So `A *_theta = H_i` with `a = a_0`.
4. By Bass–Serre theory, `H_i` acts on its Bass–Serre tree `T` with vertex
   stabilizers conjugate to `A` (finite) and one orbit of vertices and edges.
   * Every vertex has degree `[A:C] + [A:C'] = 4`, so `T` is the 4-regular tree.
   * By Švarc–Milnor, `H_i` is quasi-isometric to `T`.
   * A finitely generated group quasi-isometric to the 4-regular tree is
     hyperbolic, nonamenable (Cheeger constant is a quasi-isometry invariant
     among bounded-degree graphs) and has infinitely many ends. QED

**Proposition 5.2 (calibration).** Along this chain:

1. `p_c(H_i) < p_(2->2)(H_i) <= p_u(H_i)` for every `i`;
2. `p_c(H_i)` increases to `p_c(L)`, and `rho(H_i)` increases to `rho(L) = 1`;
3. `p_c(L) = p_u(L)`;
4. for every finite `S`, every `p >= p_c(L)`, every `n` and every `c < 1`,
   only finitely many `i` satisfy `||lambda_{H_i}(nu_i^{*n})|| <= c`;
5. for every `M` and `delta > 0`, only finitely many `i` lie in
   `U_(M,delta)`.

*Proof.*

1. **Part 1.** `fpbs-hyperbolic-nonunimodular-critical-l2-gap` (imported
   Hutchcroft) states: "`G` is quasi-transitive, nonamenable and Gromov
   hyperbolic" implies `p_c(G) < p_(2->2)(G)`. Proposition 5.1 supplies the
   hypothesis. The inequality `p_(2->2) <= p_u` is Part 3 of
   `fpbs-l2-gap-class-closed-under-local-limits`.
2. **Part 2.** This is Proposition 2.2 and Proposition 3.3. `rho(L) = 1` by
   Kesten, since `L` is amenable (metabelian).
3. **Part 3.** `fpbs-hp-relative-burton-keane` with `H = Gamma = L` amenable
   gives at most one infinite cluster for every `p`. So `p_u(L) = p_c(L)`.
4. **Part 4.** Suppose infinitely many `i` satisfied the bound. Theorem 4.2
   would give `sp_L(nu^L_{S,p}) < 1`. Then
   `fpbs-spectral-dt-certificate-bounds-connectivity-operator` Part 3 gives
   `p < p_sDT(L) <= p_(2->2)(L) <= p_u(L) = p_c(L)`, a contradiction.
5. **Part 5.** Part 3 of `fpbs-l2-gap-class-closed-under-local-limits` would
   give `p_c(L) < p_u(L)`, a contradiction. QED

**Reading.** Every approximant carries a strict L2 gap, and even
`p_u(H_i) = 1` (unimported: infinitely many ends). The approximants converge
to their limit with monotone `p_c` and monotone spectral radius. Yet no gap
reaches the limit.

* The per-approximant certificates `(S_i, n_i, c_i)` must escape: `S_i` leaves
  every ball, or `c_i -> 1`, or `n_i -> infinity`.
* Theorem 4.2 says this escape is the only thing that ever goes wrong.

This is a counterexample to any "hyperbolic approximants have gaps, hence the
limit does" principle. The only extra input such a principle could use is
nonamenability of the limit.

**Import status.** Proposition 5.1 uses textbook facts that are not Cairn
nodes:

* Bass–Serre theory for HNN extensions (Serre, *Trees*, Section I.5);
* the Švarc–Milnor lemma, and quasi-isometry invariance of hyperbolicity and
  nonamenability (Bridson–Haefliger I.8.19 and III.H.1.9).

They were not read from source in this session. So Proposition 5.2 is recorded
as calibration and is not part of the ESTABLISHED claim. What is established
is the abstract form.

**Proposition 5.3 (abstract calibration).** Let `(H_i, D)` be a surjective
chain with amenable limit `Gamma`. Then Parts 4 and 5 of Proposition 5.2 hold
for `Gamma` in place of `L`. This holds whatever gaps the `H_i` carry.

*Proof.* The proof of Proposition 5.2, Parts 3 to 5, uses only amenability of
the limit, Theorem 4.2 and the cited nodes. QED

## 6. Consequence for direct limits of hyperbolic groups (the killed class)

**Setting.**

* `free-burnside-is-a-limit-of-hyperbolic-groups` (ESTABLISHED) presents
  `B(m,N)`, for odd `N >= n_1`, as the direct limit of non-elementary hyperbolic
  quotients `F_m = G_0 -> G_1 -> ...`. "The direct limit is `G/G^N`.
  Equivalently, the kernels `ker(G -> G_k)` increase, and their union is `G^N`."
* With `D` the image of a basis, this is a surjective chain in the sense of
  Section 0.
* **Other generating sets.** Let `D'` be any finite generating set of `B(m,N)`.
  * Choose preimages in `F_m`, and let `K_k` be the subgroup of `G_k` they
    generate.
  * `ker(K_0 -> K_k) = K_0 ∩ ker(F_m -> G_k)` increases to
    `K_0 ∩ F_m^N = ker(K_0 -> B(m,N))`.
  * So `(K_k, D')` is a surjective chain with the same limit, marked by `D'`.
  * Each `K_k` is a finitely generated subgroup of a hyperbolic group.

**Corollary 6.1.** Let `Gamma` be the direct limit of a surjective chain
`(H_i, D)`, for instance `B(m,N)` with any marking. Then:

1. `p_c(Gamma) < p_sDT(Gamma)`, which gives `p_c < p_(2->2) <= p_u` on
   `Cay(Gamma, D)`, holds iff one finite datum `(S, p, n, c)` with
   `p > lim p_c(H_i)` and `c < 1` bounds `||lambda_{H_i}(nu_i^{*n})||` on
   infinitely many approximants.
2. That datum is then a certificate on every approximant.

**The class killed.** Call an approach *approximant-qualitative* if it derives
`p_c(Gamma) < p_u(Gamma)` for such a limit from theorems applied to each `H_i`
separately, with constants depending on `i`. Examples:

* the hyperbolic L2 gap (Hutchcroft);
* Choi–Seo on acylindrically hyperbolic groups;
* `p_u = 1` for infinitely-ended approximants;
* any finite-exploration or spectral certificate produced per approximant.

Every member dies at the same step: passing `i -> infinity`.

* **Invariant.** The functional `(S, p, n) -> sup_i ||lambda_{H_i}(nu_i^{*n})||`,
  which by Proposition 3.3 equals `||lambda_Gamma(nu^{*n})||`.
* **Where it dies.**
  * By Theorem 4.2, the only approximant data that reach the limit are
    uniform bounds on this functional. Such a bound is literally the
    certificate on `Gamma`.
  * Per-approximant data cannot supply it. Proposition 5.3 and the lamplighter
    chain have gaps on all approximants and none in the limit.
  * The margin is never the obstacle: `p_c(H_i) <= p_c(Gamma)` (Proposition 2.2).
* **What survives.** An argument must use a property of the limit, such as
  nonamenability, torsion or fixed price, not of the approximants.
  * Such a property must enter a uniform estimate on `||lambda_{H_i}(nu_i^{*n})||`.
  * For `B(m,N)` the natural uniform input is a uniform spectral radius bound
    `rho(G_k) <= rho(B(m,N)) < 1`, which holds by Proposition 3.3 and Adian.
  * It controls only `S = {o}`, that is `p d rho < 1`, which lies above `p_c`
    only if `p_c(B(m,N)) < 1/(d rho(B(m,N)))`. That is itself open.

## 7. Spark (not claimed)

**M3 (uniform DT margin over subgroups of hyperbolic groups).** Are there
`p* = p*(d, rho0) > 0` and, for each `eta` in `(0, p*)`, a radius `r`, a power
`n` and `c < 1`, all depending only on `(d, rho0, eta)`, with the following
property? Every Cayley graph of degree `d` of a finitely generated subgroup of
a hyperbolic group with `rho <= rho0` satisfies
`||lambda(nu_{B_r,p}^{*n})|| <= c` for all `p` in `[p_c + eta, p_c + p*]`.

For a chain with nonamenable limit, take `p = p_c(Gamma) + eta` with
`3 eta / 2 <= p*`. For large `k`, `p_c(K_k) >= p_c(Gamma) - eta/2`
(Proposition 2.2). So `p` lies in the uniform window of every late approximant,
with the same ball `B_r`.

* By Theorem 4.2 and Proposition 2.2, M3 would give `p_c < p_u` for every
  nonamenable direct limit of hyperbolic groups. That includes `B(m,N)` in all
  markings and, if presented as such limits, the Ol'shanskii monsters.
* Proposition 5.3 shows M3 needs the hypothesis `rho <= rho0 < 1`. Without it,
  the lamplighter chain is a counterexample.
