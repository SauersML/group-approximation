# Homomorphic automata over arbitrary finite group alphabets

Swarm agent `hi-spec-gottschalk-surjunctivity-conje`, 2026-09-16. Angle: special case / strengthening of
`gottschalk-surjunctivity-conjecture`.

This artifact proves `homomorphic-group-alphabet-ca-reduce-to-stable-finiteness` through the direct-proof
route `homomorphic-group-alphabet-ca-reduction-proof`. Every step is proved here. Two classical inputs are
used: the Jordan–Hölder theorem, and the compactness of a finite-alphabet full shift with its standard
consequence (a continuous map from a compact space to a discrete space depends on finitely many coordinates).
No other result is cited as an input.

## 0. Statements and what is new

**Conventions.**
- `G` is any group and `K` a finite group.
- `K^G` carries pointwise multiplication, the prodiscrete topology, and the shift `(g.x)(h) = x(g^-1 h)`.
- A cellular automaton (CA) with finite memory set `M` and local rule `mu : K^M -> K` is
  `tau(x)(g) = mu((g^-1.x)|_M)`, where `(g^-1.x)(m) = x(gm)`.
- `tau` is **homomorphic** (Phung's "group cellular automaton") when it is a group homomorphism.
  - This is equivalent to having a local rule that is a homomorphism.
  - If `mu` is a homomorphism, so is `tau`.
  - Conversely, `mu(p) := tau(x_p)(1)`, where `x_p` extends `p` by `1`, is a local rule. It is a homomorphism
    because `p -> x_p` is one.
- `P(K)` is the set of primes `p` such that `Z/p` is a composition factor of `K`.
- `LIN(G; p, n)` is the statement: every injective `F_p`-linear CA `(F_p^n)^G -> (F_p^n)^G` is surjective.

**Theorem A (reduction).** Suppose `LIN(G; p, n)` holds for every `p` in `P(K)` and every `n >= 1` with
`p^n <= |K|`. Then every injective homomorphic CA `K^G -> K^G` is surjective.

**Theorem B (linear base).** For every group `G`, prime `p` and `n >= 1`, `LIN(G; p, n)` holds if and only if
`M_n(F_p[G])` is directly finite.

**Corollary C.**
- **(a) Unconditional case.** If `K` has no abelian composition factor, then for **every** group `G` every
  injective homomorphic CA on `K^G` is bijective.
  - Examples: finite direct products of nonabelian simple groups, and wreath products `T wr_Omega Q` with
    `T` and `Q` of this kind.
- **(b) Weakly surjunctive equals linearly surjunctive.** For every group `G` the following are equivalent.
  1. `G` is weakly surjunctive: Phung, arXiv:2111.13607v2, Definition 1.2.
  2. `G` is linearly surjunctive: same paper, Definition 6.1.
  3. `F_p[G]` is stably finite for every prime `p`.
- **(c) Descent of strict witnesses.** Suppose some injective, non-surjective homomorphic CA exists on `K^G`.
  Then for some `p` in `P(K)` and some `n` with `p^n <= |K|`:
  - `M_n(F_p[G])` is not directly finite;
  - there is an injective, non-surjective `F_p`-linear CA on `(F_p^n)^G`.

**What is new relative to the graph.**
- `homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness` (ESTABLISHED) covers **solvable** `K`.
  - Its artifact, `research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md` Section 1.3 "Scope",
    says: "Extending the reduction to all finite `K` is left open."
  - Theorem A closes that gap. The derived-series filtration used there does not exist for nonsolvable `K`.
  - The replacement is the socle, which is not verbal. Preserving it requires a new first step, forcing the
    local rule to be surjective, and a new rigidity lemma for the nonabelian part.
- The solvable route cites the Ceccherini-Silberstein–Coornaert base case without re-derivation. Theorem B
  is proved in full here, so the new route has `requires: []`.
- Hypotheses are imposed only at primes of **abelian** composition factors, with rank `n <= log_p |K|`.
- Corollary C(b) reverses the inclusion {weakly surjunctive} ⊆ {linearly surjunctive} recorded in Phung's
  Section 6. So Phung's Question 1 ("Does there exist a non weakly surjunctive group?") is equivalent to the
  existence of a group `G` and a prime `p` with `F_p[G]` not stably finite.
  - Combined with the ESTABLISHED `stable-finiteness-reduces-to-prime-field`, it is equivalent to a
    counterexample to Kaplansky's stable finiteness conjecture over some field.
  - That combination is a remark. It is not used in any proof below.
- No statement of Theorem A for nonsolvable alphabets, and no proof of the converse inclusion in C(b), was
  found in the sources listed in Section 8. Novelty is claimed only relative to those sources.

## 1. Linear automata and matrices over `F_p[G]`

Put `V = F_p^n` and `R = M_n(F_p)[G]`, which is the same ring as `M_n(F_p[G])`. An element of `R` is a finite sum
`alpha = sum_h alpha_h h`, with `alpha_h` in `M_n(F_p)`.

**Lemma 1 (calculus).** Define `tau_alpha : V^G -> V^G` by `tau_alpha(x)(g) = sum_h alpha_h x(gh)`.
1. `tau_alpha` is an `F_p`-linear CA with memory set `supp(alpha)`.
2. Every `F_p`-linear CA on `V^G` is `tau_alpha` for some `alpha`.
3. `tau_alpha o tau_beta = tau_{alpha beta}`, and `tau_1 = id`.
4. `alpha -> tau_alpha` is injective.

*Proof.*
1. `tau_alpha(x)(g) = mu((g^-1.x)|_M)` with `M = supp(alpha)` and `mu(p) = sum_{m in M} alpha_m p(m)`, which is
   linear.
2. A linear local rule `mu : V^M -> V` has the form `mu(p) = sum_m A_m p(m)` with `A_m` in `M_n(F_p)`. Take
   `alpha = sum_m A_m m`.
3. Compute directly:
   `tau_alpha(tau_beta(x))(g) = sum_h alpha_h sum_k beta_k x(ghk) = sum_u (sum_{hk=u} alpha_h beta_k) x(gu)
   = tau_{alpha beta}(x)(g)`.
4. Let `x_v` be `v` at `1` and `0` elsewhere. Then `tau_alpha(x_v)(g) = alpha_{g^-1} v`, so `tau_alpha`
   determines every coefficient `alpha_h`. ∎

**Lemma 2 (= Theorem B).** `LIN(G; p, n)` holds if and only if `R` is directly finite, that is, `beta alpha = 1`
implies `alpha beta = 1`.

*Proof of "directly finite implies LIN".* Let `tau = tau_alpha` be injective and put `Y = tau(V^G)`.
1. **`tau` is a homeomorphism onto `Y`.**
   - `V^G` is compact, since `V` is finite, and Hausdorff.
   - `tau` is continuous, since each output coordinate depends on finitely many inputs.
   - So `Y` is compact, and the continuous bijection `tau : V^G -> Y` has a continuous inverse `psi : Y -> V^G`.
   - `tau` commutes with the shift: both `tau(g.x)(h)` and `(g.tau(x))(h)` equal `mu((h^-1 g.x)|_M)`. So `Y`
     is shift-invariant and `psi` is shift-equivariant.
   - `psi` is `F_p`-linear, as the inverse of a linear bijection, and `Y` is a linear subspace.
2. **A finite window decodes.** The map `Y -> V`, `y -> psi(y)(1)`, is continuous from a compact space to a
   discrete one. So it is locally constant, and by compactness there is a finite `N` in `G` such that
   `psi(y)(1)` depends only on `y|_N`.
   - Put `W = {y|_N : y in Y}`, a subspace of `V^N`.
   - Define `nu : W -> V` by `nu(y|_N) = psi(y)(1)`. This is well defined by the choice of `N`, and linear
     because `psi` is linear and restriction is linear.
   - By equivariance, `psi(y)(g) = psi(g^-1.y)(1) = nu((g^-1.y)|_N)` for all `g`.
3. **A left inverse.** Extend `nu` to a linear map `nu~ : V^N -> V`. Let `sigma` be the linear CA with local
   rule `nu~`; by Lemma 1, `sigma = tau_beta` for some `beta`.
   - For every `x`, `g^-1.tau(x) = tau(g^-1.x)` lies in `Y`.
   - So `sigma(tau(x))(g) = nu((g^-1.tau(x))|_N) = psi(tau(x))(g) = x(g)`.
   - Hence `tau_{beta alpha} = sigma o tau = id = tau_1`, and Lemma 1(4) gives `beta alpha = 1`.
4. **Surjectivity.** Direct finiteness gives `alpha beta = 1`, so `tau o sigma = tau_{alpha beta} = id`, and
   `tau` is surjective.

*Proof of "LIN implies directly finite".* Suppose `beta alpha = 1` but `alpha beta != 1`.
- `tau_beta o tau_alpha = tau_{beta alpha} = id`, so `tau_alpha` is injective.
- Suppose `tau_alpha` were also surjective. Then it is bijective with inverse `tau_beta`, so
  `tau_{alpha beta} = tau_alpha o tau_beta = id = tau_1` and `alpha beta = 1` by Lemma 1(4), a contradiction.
- So `tau_alpha` is an injective non-surjective linear CA, and `LIN(G; p, n)` fails. ∎

*Remarks.*
- The second half is the matrix case of the ESTABLISHED `stable-finiteness-failure-refutes-surjunctivity`,
  re-proved here so the route stays self-contained.
- If `M_n(F_p[G])` is directly finite, so is `M_m(F_p[G])` for `m <= n`, as a corner. This is not needed below,
  because Theorem A assumes every rank `n` with `p^n <= |K|`.

## 2. Group-theoretic lemmas

All groups in this section are finite.
- A minimal normal subgroup of `K` is a nontrivial normal subgroup containing no smaller nontrivial normal
  subgroup of `K`.
- `Soc(K)` is the subgroup generated by all minimal normal subgroups.
- Two facts about normal subgroups of an arbitrary group `H` are used repeatedly.
  - **(F1)** For normal `X, Y` of `H`, `[X, Y] <= X ∩ Y`. So distinct minimal normal subgroups of `H` intersect
    trivially and commute elementwise.
  - **(F2)** For normal `X, Y` of `H` with `X ∩ Y = 1`, `XY` is the internal direct product `X × Y`.
    - By (F1), `X` and `Y` commute elementwise, and `(x, y) -> xy` is then an isomorphism.
    - Iterating: if `N_i ∩ N_1 ... N_{i-1} = 1` for each `i`, in particular if `N_i ∩ prod_{j != i} N_j = 1`
      for each `i`, then `N_1 ... N_r = N_1 × ... × N_r`.

**Lemma 3 (minimal normal subgroups go to minimal normal subgroups).** Let `mu : K^M -> K` be a **surjective**
homomorphism and `N` a minimal normal subgroup of `K`. For `m` in `M`, let `N_m` be the subgroup of `K^M`
supported on coordinate `m` with values in `N`. Then `mu(N_m)` is either `1` or a minimal normal subgroup of `K`
isomorphic to `N`.

*Proof.*
1. `N_m` is normal in `K^M`, so `L := mu(N_m)` is normal in `mu(K^M) = K`.
2. **Normal subgroups of `K^M` inside `N_m`.** Let `J` be one. Its projection `pi_m(J)` to coordinate `m` is
   normal in `K`, because `pi_m` is surjective, and contained in `N`. So `pi_m(J)` is `1` or `N`. Since `pi_m`
   is injective on `N_m`, `J` is `1` or `N_m`.
3. **`L` is minimal.** Suppose `L != 1` and `L'` is normal in `K` with `1 != L' <= L`. Put
   `J = N_m ∩ mu^-1(L')`, which is normal in `K^M`.
   - By step 2, `J` is `1` or `N_m`.
   - `mu(J) = mu(N_m) ∩ L' = L'`: if `b = mu(a)` with `a` in `N_m` and `b` in `L'`, then `a` is in `J`.
   - So `L'` is `1` or `L`, and hence `L' = L`.
4. **`L` is isomorphic to `N`.** `ker(mu) ∩ N_m` is normal in `K^M`, so by step 2 it is `1` or `N_m`. It is not
   `N_m`, since `L != 1`. So `mu` is injective on `N_m` and `L ≅ N`. ∎

**Lemma 4 (structure of the socle).** Let `A` be generated by the abelian minimal normal subgroups of `K`, and
`S` by the nonabelian ones.
1. Every nonabelian minimal normal subgroup is a direct product of nonabelian simple groups, and has trivial
   center.
2. `S` is the internal direct product of **all** nonabelian minimal normal subgroups, and `Z(S) = 1`.
3. `A` is abelian, and `A = prod_p A_p` where `A_p` is elementary abelian of order `p^{n_p} <= |K|`. Whenever
   `A_p != 1`, `p` is in `P(K)`.
4. `A ∩ S = 1`, and `Soc(K) = A × S`.
5. For a surjective homomorphism `mu : K^M -> K`:
   - `mu(S^M) <= S`, `mu(A^M) <= A`, and `mu(A_p^M) <= A_p` for every `p`;
   - hence `mu(Soc(K)^M) <= Soc(K)`.

*Proof.*
1. **Nonabelian minimal normal subgroups.** Let `N` be minimal normal in `K` and `T` a minimal normal subgroup of
   `N`. Every `K`-conjugate `T^k` is again minimal normal in `N`.
   - Choose conjugates `T_1, ..., T_s` of `T`, as many as possible, whose product `P` is direct. `P` is normal
     in `N`.
   - For any conjugate `T^k`, `T^k ∩ P` is normal in `N` and contained in `T^k`, so it is `1` or `T^k`. If it
     were `1`, then by (F2) the product `P T^k` would be direct, contradicting maximality. So `T^k <= P`.
   - Thus `P` contains every conjugate of `T`. It is generated by conjugates, so it is normal in `K`, and
     `1 != P <= N` forces `P = N`.
   - So `N = T_1 × ... × T_s` with each `T_i ≅ T`.
   - A normal subgroup of the direct factor `T_1` is normal in `N`. Minimality of `T_1` in `N` then makes
     `T_1` simple.
   - If `N` is nonabelian, `T` is nonabelian simple, so `Z(T) = 1` and `Z(N) = prod Z(T_i) = 1`.
2. **`S` is a direct product.** Let `N_1, ..., N_r` be the distinct nonabelian minimal normal subgroups, and put
   `X = N_i ∩ prod_{j != i} N_j`.
   - `X` is normal and contained in `N_i`, so it is `1` or `N_i`.
   - If `X = N_i`, then `N_i <= prod_{j != i} N_j`, which commutes elementwise with `N_i` by (F1). So `N_i`
     would be abelian, a contradiction.
   - So `X = 1` and, by (F2), `S = N_1 × ... × N_r`. Hence `Z(S) = prod Z(N_i) = 1`.
3. **`A`.** By (F1) the abelian minimal normal subgroups commute pairwise, so `A` is abelian.
   - An abelian minimal normal subgroup `N` is elementary abelian. Choose a prime `p` dividing `|N|`. The
     elements of `N` of order dividing `p` form a subgroup, since `N` is abelian. It is nontrivial by Cauchy's
     theorem, and characteristic in `N`, hence normal in `K`. So it equals `N`.
   - Let `A_p` be generated by the abelian minimal normal `p`-subgroups. It is elementary abelian and
     `A = prod_p A_p`.
   - If `A_p != 1`, some composition series of `K` passes through the normal series `1 < A_p`, whose factors
     are `Z/p`. By Jordan–Hölder, `p` is in `P(K)`.
4. **`A ∩ S = 1`.** `A` commutes with `S` by (F1), so `A ∩ S <= Z(S) = 1`. Both are normal and together they
   generate `Soc(K)`, so `Soc(K) = A × S`.
5. **Invariance.** `S^M` is generated by the `N_m` with `N` nonabelian minimal normal and `m` in `M`. By Lemma 3
   each `mu(N_m)` is `1` or a minimal normal subgroup isomorphic to `N`, hence nonabelian, hence contained in
   `S`. The same argument gives `mu(A^M) <= A`, using abelian `N`, and `mu(A_p^M) <= A_p`, since
   `mu(N_m) ≅ N` is a `p`-group. ∎

**Lemma 5 (normal subgroups of a product of nonabelian simple groups).** Let `U = T_1 × ... × T_t` with each
`T_i` nonabelian simple. Then the normal subgroups of `U` are exactly the sub-products `prod_{i in D} T_i`, and
the minimal normal subgroups are exactly the factors `T_i`.

*Proof.* Let `X` be normal in `U` and `D = {i : T_i <= X}`.
- For each `i`, `X ∩ T_i` is normal in `T_i`, so it is `1` or `T_i`.
- For `i` not in `D`, `[X, T_i] <= X ∩ T_i = 1` by (F1). The component `x_i` of any `x` in `X` then satisfies
  `x_i t x_i^-1 = x t x^-1 = t` for all `t` in `T_i`. So `x_i` is in `Z(T_i) = 1`.
- Hence `X <= prod_{i in D} T_i <= X`.
- A sub-product is minimal normal exactly when it has one factor. ∎

## 3. The nonabelian socle layer is a permuted shift

**Lemma 6.** Let `S = T_1 × ... × T_t`, with each `T_i` nonabelian simple, let `M` in `G` be finite, and let
`nu : S^M -> S` be a homomorphism. Suppose the CA `tau_S : S^G -> S^G` with local rule `nu` is injective. Then
there are:
- elements `m_1, ..., m_t` of `M`,
- a permutation `sigma` of `{1, ..., t}`,
- isomorphisms `alpha_i : T_i -> T_{sigma(i)}`,

such that `nu(x)_{sigma(i)} = alpha_i(x(m_i)_i)` for every `x` in `S^M`. Consequently `tau_S` is bijective.

Here `s_i` is the `T_i`-component of `s` in `S`. For `s` in `T_i`, `[s]_{i,m}` is the element of `S^M` equal to
`s` at coordinate `m` and `1` elsewhere. `T_{i,m}` is the set of all `[s]_{i,m}`.

*Proof.*
1. **The kernel is a sub-product.** `S^M = prod_{(i,m)} T_{i,m}` is a direct product of nonabelian simple groups.
   By Lemma 5, `ker nu = prod_{(i,m) in D} T_{i,m}` for some set `D` of pairs.
   - Let `E` be the complement of `D` and `U_E = prod_{(i,m) in E} T_{i,m}`.
   - `S^M = ker nu × U_E`, so `nu(S^M) = nu(U_E)` and `nu` is injective on `U_E`.
2. **Every index survives.** Suppose that for some `i`, every pair `(i,m)` lies in `D`.
   - Choose `s != 1` in `T_i` and let `x` in `S^G` be `s` at `1` and `1` elsewhere.
   - For every `g`, `(g^-1.x)|_M` lies in `prod_m T_{i,m} <= ker nu`.
   - So `tau_S(x) = 1 = tau_S(1)`, contradicting injectivity.
   - Hence `c_i := #{m : (i,m) in E} >= 1` for every `i`.
3. **Order count.** `|U_E| = prod_i |T_i|^{c_i}`. Since `nu(U_E) <= S`, `|U_E| = |nu(U_E)| <= |S| = prod_i |T_i|`.
   - As every `|T_i| >= 2` and every `c_i >= 1`, each `c_i = 1`. Write `m_i` for the unique `m` with `(i,m)` in
     `E`.
   - Equality holds throughout, so `nu` is surjective and restricts to an isomorphism `U_E -> S`.
4. **Factors go to factors.** `L_i := nu(T_{i,m_i})` is normal in `S`, as the image of a normal subgroup under the
   surjection `nu`.
   - It is isomorphic to `T_i`, hence simple and nontrivial.
   - By Lemma 5 it is a sub-product; being simple, it is a single factor `T_{sigma(i)}`.
   - `sigma` is injective. If `L_i = L_j` with `i != j`, take `u != 1` in `T_{i,m_i}` and `u'` in `T_{j,m_j}`
     with `nu(u) = nu(u')`. Then `u u'^-1 != 1` lies in `U_E ∩ ker nu = 1`, a contradiction.
   - So `sigma` is a permutation.
5. **The formula.** Put `alpha_i(s) = nu([s]_{i,m_i})`, an isomorphism `T_i -> T_{sigma(i)}`.
   - Every `x` in `S^M` is the product of the commuting elements `[x(m)_i]_{i,m}`.
   - The factors with `(i,m)` in `D` are killed, so `nu(x) = prod_i alpha_i(x(m_i)_i)`.
   - The `i`-th factor lies in `T_{sigma(i)}`, so `nu(x)_{sigma(i)} = alpha_i(x(m_i)_i)`.
6. **Explicit inverse.** Therefore `tau_S(x)(g)_{sigma(i)} = alpha_i((g^-1.x)(m_i)_i) = alpha_i(x(g m_i)_i)`. Define
   `rho(y)(h)_i = alpha_i^-1(y(h m_i^-1)_{sigma(i)})`. Then:
   - `rho(tau_S(x))(h)_i = alpha_i^-1(alpha_i(x(h m_i^-1 m_i)_i)) = x(h)_i`;
   - `tau_S(rho(y))(g)_{sigma(i)} = alpha_i(rho(y)(g m_i)_i) = y(g m_i m_i^-1)_{sigma(i)} = y(g)_{sigma(i)}`.

   So `tau_S` is bijective, and its inverse is the CA `rho` with memory set `{m_i^-1}`. ∎

Injectivity of `tau_S` is used only in step 2. Without it, a surjective `nu` may keep two coordinates of one
factor and none of another. In particular, `tau_S` is bijective as soon as it is injective, **for every group `G`**,
and no algebra over `G` enters.

## 4. Proof of Theorem A

Fix `G` and write `Hyp(K)` for "`LIN(G; p, n)` for all `p` in `P(K)` and `n >= 1` with `p^n <= |K|`". The proof
is by induction on `|K|`, and the statement for `|K| = 1` is empty. Let `|K| > 1` and assume Theorem A, for this
`G`, for all finite groups of smaller order. Let `tau : K^G -> K^G` be an injective homomorphic CA with
homomorphic local rule `mu : K^M -> K`, and assume `Hyp(K)`.

**Step 0 (hypotheses pass to subquotients).**
- Concatenating composition series of the factors gives a composition series of `K^M`. By Jordan–Hölder, the
  composition factors of `K^M` are those of `K`, with multiplicities multiplied by `|M|`.
- A quotient `K^M / X` has, as composition factors, a sub-multiset of those of `K^M`: refine `1 < X < K^M` to a
  composition series.
- So `P(H) <= P(K)` for every quotient `H` of `K^M`, and in particular for `H = mu(K^M)` and for `H = K/Soc(K)`,
  which is a quotient of `K`.
- If moreover `|H| < |K|`, then `Hyp(K)` implies `Hyp(H)`.

**Step 1 (the local rule is surjective).** Put `H = mu(K^M)` and suppose `H != K`.
- Every output value of `tau` lies in `H`, so `tau(K^G) <= H^G`.
- The restriction `tau_H` of `tau` to `H^G` is a homomorphic CA with local rule `mu|_{H^M} : H^M -> H`, and it
  is injective.
- By Step 0 and induction, `tau_H` is surjective: `tau(H^G) = H^G`.
- Pick `x` in `K^G` not in `H^G`. Then `tau(x)` lies in `H^G = tau(H^G)`, so `tau(x) = tau(h)` for some `h` in
  `H^G`. Injectivity gives `x = h` in `H^G`, a contradiction.
- Hence `mu` is surjective.

**Step 2 (the socle is invariant).** Write `Soc(K) = A × S`, with `A = prod_p A_p`, as in Lemma 4.
- By Step 1 and Lemma 4(5), `mu` maps `S^M` into `S` and `A_p^M` into `A_p`, and hence `Soc(K)^M` into `Soc(K)`.
- So `tau` restricts to homomorphic CAs `tau_S` on `S^G` and `tau_{A_p}` on `A_p^G`. Both are injective.

**Step 3 (nonabelian part).** Write `S` as a product of nonabelian simple groups (Lemma 4(1),(2)). Lemma 6,
applied to `nu = mu|_{S^M}`, gives `tau(S^G) = S^G`. This step uses no hypothesis on `G`.

**Step 4 (abelian part).** Suppose `A_p != 1`.
- `A_p` is elementary abelian of order `p^{n_p} <= |K|`, so it is an `F_p`-vector space of dimension `n_p`.
- A group homomorphism between `F_p`-vector spaces is `F_p`-linear, so `tau_{A_p}` is an injective `F_p`-linear
  CA on `(F_p^{n_p})^G`.
- By Lemma 4(3), `p` is in `P(K)`, so `LIN(G; p, n_p)` is part of `Hyp(K)`.
- Hence `tau(A_p^G) = A_p^G`.

**Step 5 (the socle layer is onto).** Every `y` in `Soc(K)^G` factors pointwise as `y = (prod_p y_p) y_S`, with
`y_p` in `A_p^G` and `y_S` in `S^G`. Each factor is in the image of `tau` by Steps 3–4. Since `tau` is a
homomorphism, `tau(Soc(K)^G) = Soc(K)^G`.

**Step 6 (the quotient automaton).** Put `Z = Soc(K)`, `Q = K/Z` and `q : K -> Q`. Since `mu(Z^M) <= Z`, the map
`mu_bar(q o p) = q(mu(p))` is a well-defined homomorphism `Q^M -> Q`. The CA `tau_bar` on `Q^G` with local rule
`mu_bar` satisfies `tau_bar(q o x) = q o tau(x)`, and every configuration in `Q^G` lifts pointwise.
- **`tau_bar` is injective.** If `tau_bar(q o x) = 1`, then `tau(x)` lies in `Z^G = tau(Z^G)` by Step 5. So
  `tau(x) = tau(z)` with `z` in `Z^G`, hence `x = z` and `q o x = 1`. A homomorphism with trivial kernel is
  injective.
- `Z != 1` because `K != 1`, so `|Q| < |K|`. By Step 0, `Hyp(Q)` holds, and by induction `tau_bar` is surjective.

**Step 7 (conclusion).** Given `y` in `K^G`, choose `x` with `tau_bar(q o x) = q o y`. Then `tau(x)^-1 y` lies in
`Z^G`, so by Step 5 it equals `tau(z)` for some `z` in `Z^G`. Thus `y = tau(x) tau(z) = tau(xz)`, and `tau` is
surjective. ∎

**Where each hypothesis is consumed.**
- `LIN` is invoked only in Step 4, at pairs `(p, n_p(K'))` for the groups `K'` met in the recursion. These are
  subquotients of powers of `K` of order at most `|K|`.
- Injectivity of `tau` is used in Steps 1, 3 and 6.
- Surjectivity of `mu` (Step 1) is needed for Step 2. Section 7 records non-surjective homomorphisms for which
  the socle is not invariant.

## 5. Proofs of the corollaries

**C(a).** If `K` has no abelian composition factor, then `P(K)` is empty and `Hyp(K)` is vacuous. Theorem A gives
surjectivity of every injective homomorphic CA, so each is bijective.
- In this case the recursion of Section 4 meets only groups whose socle has `A = 1`. Only Steps 1, 3, 6 and 7 do
  any work, and `G` plays no role at all.
- **Examples.** The composition factors of `T^Omega ⋊ Q` are those of `T` and of `Q`. So finite products of
  nonabelian simple groups, and iterated permutational wreath products of them, qualify.
  - A group with a nontrivial solvable normal subgroup, or with a nontrivial abelian quotient, does not qualify.
  - For example, `SL(2,5)` has a center of order 2, and `S_5` has quotient `Z/2`.
- The case `K` nonabelian simple is elementary: a local rule is trivial or `alpha o pi_m`, as the solvable
  artifact's Scope already notes. The general case needs the socle induction.

**C(b).** Take Phung's definitions (arXiv:2111.13607v2): weakly surjunctive (Definition 1.2) and linearly
surjunctive (Definition 6.1).
- **(1) ⇒ (2).** A finite-dimensional vector space over a finite field is a finite group, and a linear CA is a
  homomorphic CA. Phung records this inclusion in Section 6.
- **(2) ⇒ (3).** `F_p^n` is a finite-dimensional space over the finite field `F_p`, so (2) gives `LIN(G; p, n)`
  for all `p` and `n`. By Lemma 2, every `M_n(F_p[G])` is directly finite, that is, `F_p[G]` is stably finite.
- **(3) ⇒ (1).** Lemma 2 gives `LIN(G; p, n)` for all `p` and `n`, and Theorem A applies to every finite `K`. ∎

*Remark (uses outside inputs; not part of the route's claim).*
- Phung's Theorem 6.4, as extracted, states: "a group G is linearly surjunctive if and only if for every field
  k, the group ring k[G] is stably finite."
- With C(b) this gives: `G` is weakly surjunctive if and only if `k[G]` is stably finite for every field `k`.
- The same conclusion follows from the ESTABLISHED `stable-finiteness-reduces-to-prime-field` (BFF24 import).
- So Phung's Question 1 asks exactly whether Kaplansky's stable finiteness conjecture fails for some group, and
  then necessarily over `F_p` for some prime `p`.

**C(c).** Contrapositive of Theorem A, followed by the second half of Lemma 2. ∎

C(c) says that a homomorphic alphabet never produces a counterexample the linear lane would miss. Moreover:
- the prime may be taken among the primes of **abelian** composition factors of `K`;
- the rank satisfies `p^n <= |K|`.

For instance, a strict homomorphic automaton over `S_5`, `A_5 × Z/2` or any 2-group descends to a strict
`F_2`-linear automaton of rank at most `log_2 |K|`.

## 6. Scope and sharpness

- **No new surjunctive group.** Theorem A concerns only automata that are group homomorphisms. Outside
  alphabets with no abelian composition factor, it is conditional on the linear gates at abelian primes.
  - It does not prove Gottschalk's conjecture for any group not already known to satisfy it.
  - It shows that the homomorphic sub-problem has no content beyond the linear one.
- **Sharp for elementary abelian alphabets.** Take `K = (Z/p)^n`. The homomorphic CAs are exactly the
  `F_p`-linear ones, so the conclusion for `K` is `LIN(G; p, n)`.
  - The hypothesis asks for `LIN(G; p, m)` for all `m` with `p^m <= p^n`.
  - By Lemma 2 and passage to corners, those follow from `LIN(G; p, n)`.
  - So for these `K`, Theorem A is an equivalence.
- **Not sharp for a single general `K`.** A strict linear automaton on `(F_p^n)^G` need not yield a strict
  homomorphic automaton over a given `K` with `p` in `P(K)` and `p^n <= |K|`. The sharp statement is the global
  one, C(b).
- **Why the rank bound is `p^n <= |K|` and not the multiplicity of `Z/p` in `K`.**
  - Step 1 applies induction to `H = mu(K^M)`, a quotient of `K^M`, which can carry more copies of `Z/p` than `K`.
  - Example: `K = A_5 × Z/2` contains `(Z/2)^3`, which is a quotient of `K^3`.
  - The conclusion of Step 1 excludes such `H`. The argument still uses the induction hypothesis at `H` to
    reach that contradiction.
  - Whether Step 1 can be proved without induction, and so the rank bound lowered, is not settled here.
- **Surjectivity of the local rule is essential to Step 2.** There are non-surjective homomorphisms
  `(A_5 × Z/2)^2 -> A_5 × Z/2` that send the central `Z/2` of one coordinate onto a non-normal subgroup of order 2
  inside `A_5`. Section 7 counts 300 homomorphisms for which the socle is not invariant.
- **Not covered.**
  - Automata that are homomorphisms only on a sub-alphabet, or `zeta`-homogeneous elsewhere. This is question 2
    of Section 8 of `research/artifacts/gk3-binary-descent-2-2026-09-14.md`.
  - Affine automata `x -> c tau(x)`, where `c` is a fixed configuration, reduce trivially to `tau`.
  - Arbitrary nonlinear automata.

## 7. Computational sanity check

This is evidence only, and the proofs above do not depend on it. The script is
`experiments/homomorphic-group-alphabet-surjunctivity-2026-09-16/check_socle_lemmas.py`, and its output is
`output.txt` in the same directory. It runs single-threaded in seconds.
- **Method.** It enumerates all homomorphisms `K -> K` from generator images, checking the homomorphism property
  on all pairs of elements.
  - The homomorphisms `K^2 -> K` are then the pairs with elementwise commuting images.
  - For each one it checks surjectivity and whether each minimal normal subgroup placed in one coordinate goes
    to `1` or to a minimal normal subgroup of the same type.

| `K` | `#Hom(K,K)` | `#Hom(K^2,K)` | surjective | invariance fails, surjective | invariance fails, non-surjective |
|---|---|---|---|---|---|
| `A_5` | 121 | 241 | 240 | 0 | 0 |
| `A_5 × Z/2` | 272 | 1264 | 720 | 0 | 300 |
| `S_4` | 58 | 148 | 48 | 0 | 0 |

- **`A_5`.** 240 is `2 × |Aut(A_5)|`. So the surjective local rules on two coordinates are exactly the maps
  `alpha o pi_m`, as in Lemma 6.
- **`A_5 × Z/2`.** The 720 surjective rules match the prediction `2 × 120 × 3`:
  - one coordinate's `A_5` maps by an automorphism;
  - the two central `Z/2`'s map to the center, not both trivially.
- **Necessity of Step 1.** The 300 non-surjective rules violating invariance show that Step 1 cannot be skipped.

## 8. Literature and novelty audit

All checks were done on 2026-09-16.

- **X. K. Phung, *Weakly surjunctive groups and symbolic group varieties*, arXiv:2111.13607v2 (5 Dec 2021).**
  - Text was extracted from the arXiv PDF by stream decompression; whitespace was lost and is restored in
    these quotes.
  - Definition 1.2: "We call a group G a weakly surjunctive group if for every finite group alphabet A, all
    injective group cellular automata τ: A^G → A^G are surjective."
  - Question 1: "Does there exist a non weakly surjunctive group?"
  - Definition 6.1: "We say that a group G is a linearly surjunctive group if for every finite dimensional
    vector space A over a finite field k, all injective linear cellular automata τ: A^G → A^G are surjective."
  - Section 6 records the chain sofic ⊆ surjunctive ⊆ weakly surjunctive ⊆ linearly surjunctive.
  - Theorem 6.4: "A group is L-surjunctive if and only if it is linearly surjunctive. In particular, a group G
    is linearly surjunctive if and only if for every field k, the group ring k[G] is stably finite."
  - Lemma 3.1: weak surjunctivity is local.
  - The paper does not prove the reverse inclusion weakly ⊇ linearly. It poses Question 1 instead.
- **arXiv full-text search `surjunctive`, newest first (35 results, newest arXiv:2606.17757).** Titles and
  abstracts were screened for weakly or linearly surjunctive groups, group CA over nonabelian alphabets, and
  stable-finiteness equivalences. Relevant abstracts were fetched individually:
  - arXiv:2111.02588, Phung, *On symbolic group varieties and dual surjunctivity* (v2 15 Nov 2021): dual
    surjunctivity of algebraic group CA over sofic groups. It does not address weak surjunctivity.
  - arXiv:2310.09451, Ceccherini-Silberstein–Coornaert–Phung, *First-order model theory and Kaplansky's stable
    finiteness conjecture*: surjunctive implies stably finite. The abstract makes no statement on weakly
    surjunctive groups.
  - arXiv:2403.05998, Phung, *Generalized Gottschalk's conjecture for sofic groups and applications*:
    perturbations of CA and twisted group rings over sofic groups. No weakly surjunctive statement.
  - arXiv:2010.04035, Phung, *On dynamical finiteness properties of algebraic group shifts*: polycyclic-by-finite
    universes. Not relevant to this question.
  - arXiv:2603.18183 (Phung, 2026), 2503.23435, 2410.17688, 2405.18287, 2209.06002 and 2111.07930 were screened
    at title and abstract-summary level only. Their full texts were **not** checked.
- **Graph imports, not re-fetched.** H. Bradford and F. Fournier-Facio, arXiv:2211.01510, through
  `stable-finiteness-reduces-to-prime-field`.
  - It is used only in the Remark of Section 5, not in any proof.
- **Ceccherini-Silberstein–Coornaert, linear surjunctivity versus stable finiteness.** The solvable route cites
  it without re-derivation. It is not used here, since Lemma 2 re-proves the case needed. The exact theorem
  number was not checked, and the reference is **unverified** for this artifact.

**Novelty statement.**
- Neither the extension of the homomorphic reduction to nonsolvable finite alphabets nor the equality
  weakly surjunctive = linearly surjunctive was found in the sources above.
- Only abstracts were screened for the 2022–2026 papers listed, so a statement buried in one of their bodies
  cannot be excluded.
- Inside the graph, the ESTABLISHED solvable node explicitly leaves the all-finite-`K` case open.
