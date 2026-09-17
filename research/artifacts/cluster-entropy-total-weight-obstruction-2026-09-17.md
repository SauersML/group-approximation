# Cluster entropy lower bounds need nonpositive total weight

Worker `a-gs-pull-8`, 2026-09-17. This artifact supports:
- the claim `cluster-entropy-lower-bounds-need-nonpositive-total-weight`, with its route `cluster-entropy-lower-bounds-need-nonpositive-total-weight-proof`;
- the Attempts entry "Cluster functionals: total weight" on `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`.

The check script is `experiments/cluster-weight-calibration-2026-09-17/check_cluster_weight.py`.

**What this replaces.** Section 2.3(1) of `research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md` asserts, without proof, that "for a group with relations the analogous Bethe functional is not an isomorphism invariant". That is a heuristic. This artifact proves a precise obstruction instead:
- **Invariant:** the total weight `kappa(F) = sum_W c_W` of the functional.
- **Test action:** a Bernoulli shift times a finite set.
- **Failing step:** the inequality `F <= H(Q)` against a cheap marker generator.

For cellular (Euler) weightings, `kappa` equals the Euler characteristic of the quotient complex.

## 0. Setting and notation

Let `G` be a countable group acting by measure-preserving maps on a standard probability space `(T, mu)`. For a finite partition `P` and a finite set `W` of `G`, put

    P^W = join_(w in W) wP.

A **finite cluster functional** is a finite formal sum

    F(P) = sum_(W in 𝒲) c_W H(P^W),

where `𝒲` is a finite family of finite nonempty subsets of `G` and the `c_W` are real. Its **total weight** is

    kappa(F) = sum_(W in 𝒲) c_W.

Since `(P^K)^W = P^(WK)`, evaluating `F` along a refinement `P^K` only uses entropies of partitions `P^(WK)`.

**Co-information form.** For a finite `U` of `G`, put

    I_U(P) = sum_(∅ ≠ V ⊆ U) (-1)^(|V|+1) H(P^V).

The coefficients of `I_U` sum to `sum_(j=1..|U|) (-1)^(j+1) binom(|U|, j) = 1`. So a functional `F = sum_U d_U I_U` has `kappa(F) = sum_U d_U`.

Examples:
- **Bowen's functional on `F_r`.** `F(Q) = (1-2r) H(Q) + sum_i H(Q join s_i Q) = I_{e}(Q) - sum_i I_{e,s_i}(Q)`, since `I_{e,s}(Q) = 2H(Q) - H(Q join sQ)` is the mutual information of `Q` and `sQ`. So `kappa = 1 - r`, which is the Euler characteristic of the rose with `r` petals: one vertex with sign `+`, and `r` edges with sign `-`.
- **Cellular weighting.** Let `X` be a complex whose cells are finite subsets of `G` (a vertex set per cell), with `G` acting freely by left translation and finitely many cell orbits. Choose one representative `sigma` per orbit and put `F_X = sum_sigma (-1)^(dim sigma) I_sigma`. Then `kappa(F_X) = chi(G\X)`. When `X` is contractible and the action is free and cocompact, this is `chi(G)`, and Atiyah's formula gives `chi(G) = sum_i (-1)^i beta_i^(2)(G)` (mentioned, not imported).

By invariance of `mu`, `I_(gU)(P) = I_U(P)`, so `F_X` depends only on the orbits.

## 1. The theorem

**Theorem 1.** Let `F` be a finite cluster functional on `G` and `(K_n)` any sequence of finite subsets of `G`. Let `𝒞` be a class of measure-preserving `G`-actions. Assume:

- **(L) Lower-bound property.** For every `T` in `𝒞` and all finite generating partitions `P`, `Q` of `T`,
  `liminf_n F(P^(K_n)) <= H(Q)`.
- **(N) Bernoulli normalization.** For some `q >= 2`, the uniform Bernoulli shift `B = (q^G, u^G)` is in `𝒞`, and with its time-zero partition `P_e`,
  `beta := liminf_n F(P_e^(K_n)) > -infinity`.
- **(Y) Finite-set products.** For infinitely many `m`, `𝒞` contains an action `B × Y_m`, where `Y_m` is an `m`-point set with uniform measure and some `G`-action by permutations. The trivial action is allowed.

Then `kappa(F) <= 0`.

(L) is the minimum any argument of the form `h^Rok(T) >= lim F(P^(K_n))` must deliver. It asks for no splitting monotonicity, no independence of `P`, no convexity of `K_n`, and no ergodicity. A maximality mechanism has `beta = log q`, but Theorem 1 only needs `beta > -infinity`.

### Proof

Fix `m` from (Y) and let `T = B × Y_m`. Let `R` be the partition of `T` into the `m` fibres `B × {c}`.

**Step 1: invariant joins shift `F` by `kappa log m`.**
- `G` permutes the atoms of `R`, so `gR = R` as a partition, and `(P_e join R)^V = P_e^V join R` for every finite `V`.
- `R` is independent of the Bernoulli coordinates and uniform, so `H(P_e^V join R) = H(P_e^V) + log m`.
- Therefore
  `F((P_e join R)^(K_n)) = sum_W c_W (H(P_e^(W K_n)) + log m) = F(P_e^(K_n)) + kappa log m`.
- `P_e join R` generates `T`, because `P_e` generates `B` and `R` separates the fibres. So
  `liminf_n F((P_e join R)^(K_n)) = beta + kappa log m`.

(Check 2 of the script verifies the shift identity by exact enumeration.)

**Step 2: a cheap marker generator.**
- Fix `0 < eps < 1`. Let `E_0` be a cylinder set of `B` with `u^G(E_0) = eps'`, where `eps' <= eps`. For example, take the set where `x(g) = 0` on a finite set of size `k`, with `q^-k <= eps`. Put `E = E_0 × Y_m`.
- Define `R_E = {E^c} ∪ {E_0 × {c} : c in Y_m}` and `Q = P_e join R_E`.
- **Generation.** `B` is ergodic (it is mixing) and `E_0` has positive measure. So for a.e. `(x, c)` there is `g` with `g x in E_0`, and then `g (x, c) = (g x, g c)` lies in the atom `E_0 × {g c}`. The `R_E`-name of `(x, c)` at `g` therefore reveals `g c`, hence `c`. Together with `P_e`, `Q` separates points modulo null sets, so it generates `T`.
- **Entropy.** `H(Q) <= H(P_e) + H(R_E) = log q + h(eps') + eps' log m`, where `h(t) = -t log t - (1-t) log(1-t)`. (Check 3 of the script.)

**Step 3: compare.** (L), applied to the generating pair `P_e join R`, `Q`, gives for every admissible `m` and every cylinder measure `eps' = q^-k`

    beta + kappa log m <= log q + h(eps') + eps' log m.

Let `k -> infinity`. Then `h(eps') + eps' log m -> 0`, so

    beta + kappa log m <= log q        for every admissible m.            (*)

Since `beta` is finite and `m` takes infinitely many values, dividing by `log m` gives `kappa <= 0`. QED

**Remark (one `m` suffices at maximal normalization).** If `beta >= log q`, as in a maximality mechanism, (*) with a single `m >= 2` already gives `kappa <= 0`. So (Y) can be weakened to "some `m >= 2`".

### Variants

1. **Sequences of functionals.** If `F_n` has total weight `kappa_n -> kappa` and (L), (N) hold with `F_n(P^(K_n))` in place of `F(P^(K_n))`, the same proof gives `kappa <= 0`.
   - Kolmogorov–Sinai entropy `H(P^(F_n))/|F_n|` over Følner sets has `kappa_n = 1/|F_n| -> 0`.
   - Bowen's functional has `kappa = 1 - r`.
   Both pass.
2. **Ergodic classes.** Take `Y_m = G/L` for a subgroup `L` of index `m`. Then `B × G/L` is free and ergodic, since it is the product of a mixing action and an ergodic one. So Theorem 1 applies to classes of free ergodic actions:
   - at maximal normalization, as soon as `G` has one proper finite-index subgroup;
   - otherwise, when `G` has finite-index subgroups of unbounded index.
3. **Quantitative form.** (*) says `kappa <= (log q - beta)/log m` for each admissible `m`.

## 2. The cellular corollary and a witness

**Corollary 2.** Let `X` be a cell complex whose cells are finite subsets of `G`, with `G` acting freely on cells and with finitely many orbits, and let `F_X = sum_sigma (-1)^(dim sigma) I_sigma`. If `chi(G\X) > 0`, then `F_X` has no lower-bound property (L) on any class containing `B` and `B × Y_m` for infinitely many `m`. This holds whatever exhaustion `(K_n)` is used and whatever the value of `beta`.

**Bernoulli value of a cellular functional.** In the convention `(g x)(h) = x(g^-1 h)`, `g P_e` reads the coordinate at `g`. So `P_e^K` is the coordinate partition on `K`, and `u P_e^K` is the coordinate partition on `uK`. Co-information of coordinate partitions of an i.i.d. uniform field is the counting measure of the intersection (Check 1):

    I_sigma(P_e^K) = |∩_(u in sigma) uK| log q = #{h : sigma^-1 h ⊆ K} log q.

Summing over orbit representatives, `F_X(P_e^K) = chi(X[K^-1]) log q`, where `X[S]` is the full subcomplex on the vertex set `S`. So on exhaustions by symmetric sets with contractible full subcomplexes, the cellular functional has exactly the Bernoulli normalization `beta = log q`.

**Witness (elementary, fully checked).** Let `G = F_2 × F_2 = <a, b> × <c, d>`, and let `X` be the product of the two Cayley trees:
- vertices `g`;
- edges `{g, g s}` for `s in {a, b, c, d}`;
- squares `{g, g s, g t, g s t}` for `s in {a, b}` and `t in {c, d}`.

The cells:
- **Quotient.** The quotient has 1 vertex, 4 edge orbits and 4 square orbits, so `kappa = chi(G\X) = 1 - 4 + 4 = 1`.
- **Normalization.** `K_n = B_n × B_n` (product of word balls) is symmetric, and `X[K_n]` is a product of two finite trees, so `chi = 1` and `F_X(P_e^(K_n)) = log q` for every `n`. The script confirms `chi(X[B_n × B_n]) = 1` for `n <= 4` by direct cell count (Check 4).
- **Failure.** On `B × Y_2` with the trivial action, `F_X((P_e join R)^(K_n)) = log q + log 2`, while `H(Q) <= log q + h(eps) + eps log 2 -> log q`. The table in Check 5 shows larger `m`: for `q = 2`, `eps = 10^-3` and `m = 10^9`, `21.416` against `0.722`.

So the product-of-trees analogue of Bowen's functional passes the Bernoulli normalization and fails (L). It fails already on a nonergodic product with a finite set, before any question of isomorphism invariance arises. Bowen's functional on `F_r` satisfies `kappa = 1 - r <= 0` and is not touched.

**Kazhdan examples (mentioned, not imported).**
- **Groups.** Torsion-free cocompact lattices in `Sp(n,1)` with `n >= 2`, and in `F_4^(-20)`, are hyperbolic Kazhdan groups.
- **Positive Euler characteristic.** They act freely and cocompactly on contractible symmetric spaces of dimension `4n` (resp. 16) whose compact duals have positive Euler characteristic, so `chi(G) > 0`.
- **Vertex-set complex.** For torsion-free hyperbolic `G`, the Rips complex `R_d(G)` with `d >= 4 delta + 2` is contractible, with free cocompact action on simplices and vertex set `G`. `chi(G)` does not depend on the chosen complex.

On such groups every Euler-weighted cellular f-type functional has `kappa > 0` and dies by Theorem 1. The groups are residually finite, so the ergodic variant applies too. Only the `F_2 × F_2` witness is used as evidence in the claim.

For contrast, Kazhdan groups have `beta_1^(2) = 0` (mentioned, not imported). The degree-1 term that makes `chi(F_r) = 1 - r` negative, and so keeps Bowen's functional alive, is therefore absent. A cellular functional on a Kazhdan group has `kappa = beta_0^(2) - 0 + beta_2^(2) - ...`, with `beta_0^(2) = 0` for infinite `G`, and its sign is set by higher `l^2`-Betti numbers.

## 3. What survives, stated honestly

Theorem 1 kills positive-weight functionals only for mechanisms whose class `𝒞` contains products with finite sets. The following escape it:

1. **Ergodic-only mechanisms on groups without finite actions.** A fg simple Kazhdan host has no nontrivial finite actions. So the ergodic variant is unavailable there, and the kill applies only to mechanisms claimed for all pmp actions with finite generating partitions, nonergodic ones included.
   - Bowen's invariance theorem is of this all-actions type, and so is every splitting argument that passes from `P^(K_n)` to `P^(K_(n+1))` without using ergodicity. Those are all killed when `kappa > 0`.
   - A mechanism that uses ergodicity essentially is not.
   - Replacing `Y_m` by an ergodic action with an approximately invariant `m`-set partition is not available on hosts with no compact actions. This is a genuine gap, not a technicality.
2. **Functionals with `kappa <= 0`.** For these the test gives no information. On a Kazhdan host, Euler-weighted cellular functionals have `kappa = chi(G)`, which can be `0` (for example, torsion-free lattices in `SL_3(R)`, where the ranks of `G` and `K` differ; mentioned, not imported) or negative in other dimensions. Those survive Theorem 1 and must be handled by other obstructions.
3. **Non-cluster mechanisms.** Rokhlin entropy itself, Kolmogorov–Sinai and sofic entropy are not finite cluster functionals. Their normalized approximants have total weight tending to `0`.

## 4. Relation to a-gs-pull-7

Worker `a-gs-pull-7` posted the lemma `cluster-entropy-functionals-vanish-on-one-ended-bernoulli` on the live bus (2026-09-17). It is not landed in this worktree, so it is not linked by id.

| | a-gs-pull-7 | this artifact |
|---|---|---|
| Hypothesis on `F` | splitting-monotone, `F(beta join t^-1 gamma) <= F(beta)` | none beyond (L) |
| Hypothesis on `G` | one-ended, finitely generated | any countable group |
| Test action | every Bernoulli shift | Bernoulli × finite set |
| Invariant | `psi(B) = sum_W c_W |BW|` | `kappa(F) = sum_W c_W` (= `chi` for Euler weights) |
| Failing step | Bernoulli normalization: `lim F(Q_(B_n)) <= 0` | lower bound `F <= H(Q)` against the marker generator |

The two results combine as follows:
- On a one-ended Kazhdan host, a Bowen-style mechanism (monotone) cannot normalize Bernoulli shifts (pull-7).
- A non-monotone mechanism with positive total weight cannot be a lower bound on the all-actions class (Theorem 1).
- A surviving cluster mechanism must therefore be non-monotone, and either have `kappa <= 0` or use ergodicity essentially.

This strengthens condition 5 of Section 4 of the 2026-09-12 artifact. There, the tree failure was only described heuristically. Now the Euler-weight generalization of the tree is dead whenever `chi > 0`, for a stated reason.
