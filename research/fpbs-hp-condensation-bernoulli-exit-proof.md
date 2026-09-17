---
rg: 2
id: fpbs-hp-condensation-bernoulli-exit-proof
kind: route
title: Spectral gap of Bernoulli kills thinning at positive frequency, hyperfinite block coins pass to the weak limit, and monotone cost transfers the frequency bound
target: fpbs-hp-condensation-bernoulli-exit
requires:
  - cost-is-constant-on-weak-equivalence-classes
---

Full written proof. Imported inputs:

- **[K]** Kechris, *Global aspects of ergodic group actions*.
  - Weak containment of actions implies weak containment of the Koopman representations on `L^2_0`, and products
    and factors respect weak containment.
  - Corollary 10.14: for finitely generated `Gamma` and free actions, `a ≺ b` implies `C(a) >= C(b)`. This is the
    required node.
- **[HP]** Hutchcroft--Pete, arXiv:1810.11015, read 2026-09-17 from the arXiv HTML:
  - Proposition 2.2: `mu_i` has marginal `p` and converges weak-star to `p delta_all + (1-p) delta_empty`.
  - Lemma 2.3: there is a Borel `Gamma`-invariant frequency function such that, for simple random walk `X_n` from
    `e` independent of `omega`, `(1/N) sum_{n<N} 1{X_n in C} -> freq(C)` for every cluster `C`, almost surely.
  - Definition of `i_freq`.
  - Theorem 1.1 with its proof: `i_freq(p) < infinity` for property (T) groups.
- **[G]** Gaboriau induction formula: for a Borel complete section `A`, the unnormalized costs satisfy
  `C(R) = C(R|A) + mu(X \ A)`.
- **[KM]** Kechris--Miller, *Topics in orbit equivalence*: an aperiodic countable Borel equivalence relation has
  Borel complete sections of arbitrarily small measure.
- Kesten: `rho = ||lambda(m)|| < 1` for nonamenable `Gamma`. The Koopman representation of `b` on `L^2_0` is a
  multiple of `lambda`.

**Conventions.**
- The shift is `(g omega)(h) = omega(g^{-1} h)`, and the Koopman operator is `kappa(g) f = f ∘ g^{-1}`.
- For `f = omega(e) - p` in `L^2_0(mu)`, `<kappa(g) f, f> = Cov_mu(omega(g), omega(e))`.
- `X_n = s_1 ... s_n` has law `m^{*n}`, and `m^{*n}` is symmetric.
- `tau_mu(g) = mu(e and g lie in one cluster)`, where a cluster contains only occupied vertices.

## 0. `W_b` is weak-star closed

**Claim.** Let `K` be compact metrizable and let `nu_n -> nu` be invariant laws on `K^Gamma` with each shift
`s_{nu_n} ≺ b`. Then `s_nu ≺ b`.

*Proof.*
1. By the definition of weak containment ([K]), we must match, for every finite partition `P`, finite `F` and
   `epsilon > 0`, the numbers `nu(g P_i ∩ P_j)` for `g` in `F` by some partition of `b` within `epsilon`.
2. Approximate `P` in `nu`-measure by a partition `P'` into finite unions of cylinder sets built from `nu`-continuity
   sets of the one-coordinate marginal. Such products have `nu`-null boundary.
3. Then `nu_n(g P'_i ∩ P'_j) -> nu(g P'_i ∩ P'_j)`, and `s_{nu_n} ≺ b` supplies the matching partition of `b`.

Factors of an action weakly contained in `b` are weakly contained in `b`, and so are products of such actions, since
`b x b ≅ b`. So `W_b`, identified with the laws `nu x Leb^Gamma` of `(omega, w)`, is closed, and it is closed under
factor maps and independent joins.

## A. Spectral bound

1. If `mu` is in `W_b`, then `s_mu x b ≺ b`. So the Koopman representation `kappa` on `L^2_0(mu)`, a
   subrepresentation of `L^2_0(mu x b)`, is weakly contained in `lambda^infinity` ([K]).
2. Norms of group-algebra elements do not increase under weak containment, so `||kappa(m)|| <= rho`.
3. Hence `|<kappa(m^{*n}) f, f>| <= rho^n ||f||^2` for every `f` in `L^2_0(mu)`.
4. With `f = omega(e) - p`, this is the stated bound. Also, `L^2_0` has no almost-invariant vectors, so `s_mu x b`
   is ergodic.

**Finiteness of `i_*`.**
1. If `mu_i^q` were in `W_b` for every `i`, then every `mu_i` would be in `W_b`, inductively by union closure (§C).
2. By [HP] Proposition 2.2, `Cov_{mu_i}(omega(e), omega(s)) -> p(1-p)` for each `s` in `S`.
3. So `sum_s m(s) Cov_{mu_i}(e,s) > rho p(1-p)` for large `i`, contradicting (A) with `n = 1`.
4. Using `Cov = p(1-p) - D/2`, where `D(s) = mu(omega(e) != omega(s))`, the violated condition is: average
   disagreement `< 2(1-rho) p(1-p)`.

## B. Frequency exit

Let `eta` be the `q`-thinning of `omega ~ mu`.

1. For `g != e`, the pair `e, g` is retained with probability `q` if `e ~ g`, and with probability `q^2` if both are
   occupied but not connected. Therefore:
   - `E[eta(e) eta(g)] = q^2 (mu(omega(e) = omega(g) = 1) - tau_mu(g)) + q tau_mu(g)`;
   - `Cov_{mu^q}(e,g) = q^2 Cov_mu(e,g) + q(1-q) tau_mu(g)`.
   The same identity holds at `g = e`.
2. Sum against `m^{*n}`. We have `sum_g m^{*n}(g) tau_mu(g) = E_{mu x P_e}[1{X_n in C_e(omega)}]`.
3. Suppose `mu` and `mu^q` are both in `W_b`. Apply (A) to both. The marginal of `mu^q` is `qp`. This gives
   `q(1-q) E[1{X_n in C_e}] <= rho^n (qp(1-qp) + q^2 p(1-p))`, so the Cesàro means of `E[1{X_n in C_e}]` tend to `0`.
4. By [HP] Lemma 2.3 and bounded convergence, those Cesàro means tend to `E_mu[freq(C_e)]`.
5. That limit is positive: `mu(F) > 0`, and by invariance of `freq`, `e` lies in a positive-frequency cluster with
   positive probability. This is a contradiction.

## C. Hyperfinite thinning stays in `W_b`

**Setup.**
- Let `X = {0,1}^Gamma x [0,1]^Gamma` carry `mu x Leb`, with `x = (omega, u)`.
- The cluster relation is `S_mu = {(x, g^{-1} x) : omega(e) = omega(g) = 1, e ~ g in omega}` on
  `A_e = {omega(e) = 1}`. The root of `g^{-1} x` is the vertex `g` of `omega`.
- Assume `S_mu = union_n F_n`, with `F_n` increasing finite Borel equivalence relations, off a null set.
- Adjoin independent uniform fields `u'`, `v`, `w`.

**Construction.**
1. The block of an occupied vertex `g` is `B_n(x,g) = {d : omega(d) = 1, (g^{-1} x, d^{-1} x) in F_n}`. It is
   finite and equivariant: `B_n(hx, hg) = h B_n(x,g)`.
2. Let `d*` minimise `u'` over the block, and put `c_n(g) = 1{v(d*) < q}` and `eta_n(g) = omega(g) c_n(g)`.
3. The law `nu_n` of `(eta_n, w)` is a factor of `s_mu x b x b x b`. That action is weakly contained in
   `b x b x b x b ≅ b`, so `nu_n` is in the closed class of §0.

**Window convergence.**
1. Conditionally on `(x, u')`, distinct blocks have distinct representatives, and `v` is independent. So the coins
   restricted to a finite window `W` are i.i.d. Bernoulli(q) over the blocks meeting `W`.
2. Since `F_n` increases to `S_mu` and `W` is finite, almost surely the blocks and the clusters induce the same
   partition of the occupied part of `W` for all large `n`.
3. Hence the `W`-marginal of `nu_n` converges in total variation to the `W`-marginal of `mu^q x Leb`. So `nu_n`
   converges weak-star to `mu^q x Leb`, and by §0, `mu^q` is in `W_b`.

Only the hyperfiniteness of the subrelation whose classes carry the coins was used. So the general statement holds
for any hyperfinite Borel subrelation of `S_mu`.

**Union.** If `mu` and `mu'` are in `W_b`, the union of independent samples, joined with `b`, is a factor of
`(s_mu x b) x (s_mu' x b)`. That product is weakly contained in `b x b ≅ b`.

**Invariance of hyperfiniteness.** Hyperfiniteness of `S_mu` does not depend on the independent noise adjoined. The
lift through a class-bijective factor map preserves amenability in both directions, and amenability is equivalent
to hyperfiniteness (Connes--Feldman--Weiss).

## D. Cost transfer from positive frequency

Let `mu` be in `W_b` with `mu(F) > 0`, and let `R` be the orbit relation of the free action `s_mu x b`.

**Maximal-frequency clusters.**
1. By §A, `R` is ergodic, so `mu(F) = 1`.
2. By ergodicity, `f_max = max_C freq(C)` is almost surely a constant `> 0`.
3. Since `sum_C freq(C) <= 1` (Cesàro sums over disjoint clusters), the number `N` of maximal-frequency clusters is
   at most `K = floor(1/f_max)`.
4. Let `A = {x : omega(e) = 1, freq(C_e) = f_max}`. It is a Borel complete section.
5. Maximal-frequency clusters are infinite, so `S_mu|A` is aperiodic, and `R|A` contains `S_mu|A` with at most `K`
   classes per `R|A`-class.

**Cluster graphing.**
1. For each `s` in `S`, define the partial map `phi_s(x) = s^{-1} x` on `A ∩ {omega(s) = 1}`. It lands in `A`,
   because adjacent occupied vertices share a cluster.
2. The graphing `{phi_s}` generates `S_mu|A`, since clusters are connected in the Cayley graph.
3. Its cost is `(1/2) E[1{e in A} #{s : omega(s) = 1}] <= |S|p/2`.

**Cross edges.**
1. By [KM], choose a Borel complete section `B` of `S_mu|A` with `mu(B) <= delta/K`.
2. Enumerate `Gamma = {g_1, g_2, ...}`. For `x` in `B`, let `psi_j(x) = g_k^{-1} x`, with `k` minimal such that the
   point lies in `B` and is not `S_mu`-related to `x, psi_1(x), ..., psi_{j-1}(x)`, whenever such a `k` exists.
   These maps are Borel, and their total cost is `<= K mu(B) <= delta`.
3. Two points of `A` in one `R`-class are joined by a path: first inside the cluster to a point of `B`, then by one
   `psi_j` edge into the other maximal-frequency cluster, then inside that cluster.
4. So `C(R|A) <= |S|p/2 + delta`.

**Conclusion.**
1. By [G], `C(s_mu x b) = C(R|A) + mu(X \ A) <= 1 + |S|p/2 + delta` for every `delta`.
2. Since `s_mu x b ≺ b` and both actions are free, [K] Corollary 10.14 gives `C(b) <= C(s_mu x b)`.

## E. Dichotomy

1. §A gives `i_* < infinity`, and every `mu_i` with `i <= i_*` is in `W_b`.
2. **If `i_freq <= i_*`.** Then `mu_{i_freq}` is in `W_b` with positive frequency. By §B, `mu_{i_freq}^q` is not in
   `W_b`, so `i_* <= i_freq` and hence `i_* = i_freq`. §D gives `C(b) <= 1 + |S|p/2`. This is (I).
3. **Otherwise `i_* < i_freq`.** Then `mu_{i_*}` is in `W_b`, so it is ergodic, and it has no positive-frequency
   cluster. By §C, its cluster relation is not hyperfinite, since `mu_{i_*}^q` is not in `W_b`. This is (II).
4. **Kazhdan reduction.** For an infinite Kazhdan `Gamma`, `i_freq < infinity` ([HP]). Alternative (I) along
   `p -> 0` gives `C(b) = 1`. Every free action `a` has `b ≺ a` (Abert--Weiss), so `1 <= C(a) <= C(b) = 1`.
5. **Free groups.** For `F_r`, `C(b) = r` and `|S| = 2r`. So (I) is impossible for `p < 1 - 1/r`.

**Scope.** This is a written deduction over the imported theorems above, and the imports have not been re-verified
here. The reduction is one direction only.
