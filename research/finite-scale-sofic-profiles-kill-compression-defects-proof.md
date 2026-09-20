---
rg: 2
id: finite-scale-sofic-profiles-kill-compression-defects-proof
kind: route
title: Kun--Thom's centralizer proof with its only ambient inputs, the Proposition 3.1 matching and Lemma 4.4, replaced by a tight-cluster matching and fixed-algebra mass transport
target: finite-scale-sofic-profiles-kill-compression-defects
requires:
  - finite-scale-compressors-preserve-kazhdan-fixed-algebras
  - bounded-cluster-period-preserves-kazhdan-fixed-algebras
  - ambient-decomposition-kun-thom-normalization
artifacts:
  - research/artifacts/kun-thom-2608-06222-section4-finite-scale-excerpts.md
  - research/artifacts/kun-thom-2608-06222-section4-ambient-audit.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**Proof import with two substitutions.** This route imports the proof of Kun--Thom
Theorem 4.1 (arXiv:2608.06222v1, Section 4) under the trust surface already accepted by
`ambient-decomposition-kun-thom-normalization-audit`. That audit shows that the proof
reaches the ambient partition in exactly two places:
- the Proposition 3.1 component matching, invoked in the first paragraph of the proof of
  Lemma 4.3 (excerpt K2 of the finite-scale excerpts artifact);
- the two applications of Lemma 4.4 in the main proof (K4, K5).

Step 1 below replaces the first by a matching built from `sigma|_L` and `u_n` alone.
Step 4 replaces the second by item 3 of `finite-scale-compressors-preserve-kazhdan-fixed-algebras`.
Every other step is imported unchanged. Both substitutes are proved here in full, from
established nodes.

## Setting

The setting is that of the target claim. Fix `s in Comp_G(L)` and write `u_n = sigma_n(s)`.
Put `H = <L, s>` and restrict `sigma` to `H`. Kun--Thom's main proof is run with the single
compressor `t_1 = s` and `Gamma = L` (K1 with `m = 1`, words `w_(1,x)` representing
`s x s^-1 in L` for `x in S`).

On the cluster frame `Q_n = {Q_i : i in I_n^0}` (index `n` suppressed), `pi(i)` is the
dominant target, maximizing `|u Q_i ∩ Q_j|` over `j`. The loss is
`ell(i) = |Q_i| - |u Q_i ∩ Q_(pi i)|`, and `Lambda_n = sum_i ell(i) = lambda_n |Y_n|`.
Item 1 of `bounded-cluster-period-preserves-kazhdan-fixed-algebras` gives
`lambda_n ->_U 0`. Cluster weight is `nu(A) = sum_(i in A) |Q_i| / |Y_n|`, and
`phi(y) = log |Q(y)|`.

## Step 1. Tight-cluster matching under (FS-size)

**Lemma M.** Assume (FS-size). There are `theta_n, eta_n ->_U 0` and a set `T_n` of
clusters with `nu(T_n) ->_U 1` such that, for `U`-almost every `n`:
1. `pi` is injective on `T_n`;
2. for `i in T_n`, `(1 - theta_n)|Q_i| <= |Q_(pi i)| < e^(eta_n) |Q_i|`;
3. for `i in T_n`, `|u Q_i △ Q_(pi i)| <= (2 theta_n + e^(eta_n) - 1) |Q_i|`;
4. `nu(pi(T_n)) >= (1 - theta_n) nu(T_n) ->_U 1`.

The matching `pi|_(T_n)` depends only on `sigma|_L`, the frame and `u_n`. It does not depend on
any groupoid choice.

*Proof.* Fix `0 < theta <= 1/2` and `eta > 0`.

(a) *Exceptional set.* Call `i` bad if `ell(i) > theta |Q_i|`. Let `B_theta` be the points of
bad clusters, together with the points `y in Q_i` with `u y ∉ Q_(pi i)`. Bad clusters carry
fewer than `Lambda_n / theta` points. The second kind number exactly
`sum_i ell(i) = Lambda_n`. So `|B_theta| <= Lambda_n (1/theta + 1)`.

(b) *One-sided inequality.* Let `y ∉ B_theta` with `y in Q_i`. Then `i` is good and
`u y in Q_(pi i)`, so `phi(u y) = log |Q_(pi i)|`. Moreover
`|Q_(pi i)| >= |u Q_i ∩ Q_(pi i)| = |Q_i| - ell(i)`. Put `x = ell(i)/|Q_i| <= 1/2`. Since
`-log(1 - x) <= 2x` there,
`phi(u y) >= phi(y) - kappa(y)` with `kappa(y) = 2 ell(i)/|Q_i|`. Summing over the points of
`Q_i` gives at most `2 ell(i)`, so `sum_(y ∉ B) kappa(y) <= 2 Lambda_n`.

(c) *Mass transport.* Let `J_(theta,eta) = {y ∉ B_theta : phi(u y) >= phi(y) + eta}`. Given
`eps > 0`, (FS-size) gives `k` and `R` such that, for `U`-almost every `n`, intervals
`[a_1, a_1 + R], ..., [a_k, a_k + R]` carry `phi`-mass `>= 1 - eps`. Apply item 1 of the
fixed-algebra node to each interval, with `E = B_theta`, `a = a_r` and `b = a_r + R + eta`:

    eta · #{y ∉ B : a_r <= phi(y) <= a_r + R, phi(u y) >= phi(y) + eta}
        <= (R + eta)|B_theta| + 2 Lambda_n.

Summing over `r` and adding the uncovered mass gives

    |J_(theta,eta)| / |Y_n| <= eps + k [ (R + eta)(1/theta + 1) + 2 ] lambda_n / eta.

(d) *Diagonal choice.* For `m >= 2` put
`a_m(n) = |B_(1/m) ∪ J_(1/m,1/m)| / |Y_n|`. By (a), (c) and `lambda_n ->_U 0`,
`lim_U a_m(n) <= eps` for every `eps`, so `lim_U a_m(n) = 0`. Hence
`A_m = {n : a_j(n) < 1/m for 8 <= j <= m}` lies in `U` for `m >= 8`, and it decreases in `m`.
Put `m(n) = max{m in [8, n] : n in A_m}`, and `m(n) = 8` if there is none. For each `M >= 8`,
`{n : m(n) >= M} ⊇ A_M ∩ [M, inf)` lies in `U`. So `m(n) ->_U inf`, and
`a_(m(n))(n) < 1/m(n)` for `U`-almost every `n`. Set `theta_n = eta_n = 1/m(n)`.

(e) *Tight clusters.* Call `i` tight if `ell(i) <= theta_n |Q_i|` and
`|Q_(pi i)| < e^(eta_n) |Q_i|`. Let `T_n` be the set of tight clusters. A point
`y ∉ B ∪ J` lies in a good cluster `Q_i` with `u y in Q_(pi i)`, and
`log |Q_(pi i)| = phi(u y) < phi(y) + eta_n`. So `Q_i` is tight, and
`nu(T_n) >= 1 - a_(m(n))(n) ->_U 1`. The lower bound in 2 is
`|Q_(pi i)| >= |Q_i| - ell(i)`.

(f) *Injectivity.* Suppose `i != i'` are tight with `pi i = pi i' = j`. Then `u Q_i` and
`u Q_(i')` are disjoint, and each meets `Q_j` in at least
`(1 - theta_n)|Q_i| > (1 - theta_n) e^(-eta_n) |Q_j|` points. Since `m(n) >= 8`,
`(1 - 1/8) e^(-1/8) > 0.77 > 1/2`, which is a contradiction.

(g) *Symmetric difference.*
`|u Q_i △ Q_(pi i)| = |Q_(pi i)| - |Q_i| + 2 ell(i) <= (e^(eta_n) - 1 + 2 theta_n)|Q_i|`.

(h) *Image weight.* By (f) and the lower bound in 2,
`nu(pi(T_n)) = sum_(i in T_n) |Q_(pi i)| / |Y_n| >= (1 - theta_n) nu(T_n)`. ∎

## Step 2. Lemma 4.3 with Lemma M in place of the Proposition 3.1 matching

The first paragraph of the proof of Lemma 4.3 (K2) consumes four properties of the
Proposition 3.1 matching (K3) of the full partitions `{u Q_i}` and `{Q_j}` over `I_n^0`:
- (i) it is injective on a family of cells covering all but `o_U(|Y_n|)` points;
- (ii) its total symmetric difference is `o_U(|Y_n|)`;
- (iii) it changes component sizes by a factor `1 + o_U(1)`;
- (iv) its total error is a sequence fixed before the cluster scale is chosen.

`pi|_(T_n)` has all four:
- (i) is items 1 and 4 of Lemma M.
- (ii) follows from item 3: the sum is at most `(2 theta_n + e^(eta_n) - 1)|Y_n|`.
- (iii) is item 2.
- (iv) holds because `pi|_(T_n)` and its error are built from `sigma|_L`, the frame and
  `u_n` alone.

The error sequences are the matching error from (ii), the weight `1 - nu(T_n)`, and the label
discrepancy of the words `w_(1,x)`. The last one is a property of `sigma|_H` only. (FS-groupoid)
lets us prescribe all three before the scales are chosen, so Lemma 4.2 supplies an admissible
groupoid choice for which they are `o_U(eps_n)` and `log o_n`, `log k_n` satisfy (FS). This is
the use of K1's last sentence that K2 makes.

The rest of the proof of Lemma 4.3 is imported unchanged. The audit route finds no further use
of the ambient partition in it. By audit excerpts E and F, the only ambient mentions before
Lemma 4.4 are the convention at lines 854–861 and the matching import at lines 898–902. This gives the conull
bijection `pi_n : D_n -> R_n` with `|u Q_i △ Q_(pi_n i)| <= delta_n |Q_i|`, the relative cluster
functor `F_n`, and `pi_n = pi` on `D_n ⊆ T_n ∩ I_n`. Here `pi_n` is the dominant target
restricted to `D_n`, because K2 only deletes pairs.

## Step 3. The one-sided inequalities

These are imported unchanged from the main proof, lines 1124–1188 (K5 and the audit). For `i`
in `D_n`, outside a family of components of weight `o_U(1)`:

    o_n(pi_n i) <= (1 + kappa_n) o_n(i),        k_n(pi_n i) <= k_n(i),

with `kappa_n ->_U 0`. The second inequality comes from the faithful functor
`C_n(pi i, pi i) -> C_n(i, i)` supplied by `F_n`. Neither uses the ambient partition. K5 records
that they have "exactly the exceptional-set form required in" Lemma 4.4.

## Step 4. Item 3 of the fixed-algebra node in place of Lemma 4.4

Take `f_n = o_n`, and then `f_n = k_n`, extended by `1` on clusters outside `I_n` as in K4. Both
are positive. Let `Bad_n` be the clusters outside `D'_n`, where `D'_n ⊆ D_n` removes the
weight-`o_U(1)` exceptional family of Step 3. Then `nu(Bad_n) ->_U 0` by Step 2.

Check the hypotheses of item 3 at the compressor `u = s`, using the frame and its dominant
target `pi`:
- On `i ∉ Bad_n` we have `pi i = pi_n i`, so the inequality of Step 3 is the required
  `f_n(pi_n i) <= (1 + kappa_n) f_n(i)`, with `kappa_n = 0` for `k_n`.
- `X_n` is the points of `Bad_n` clusters together with the points `y` with `u_n y ∉ Q_(pi i)`.
  So `|X_n| <= nu(Bad_n)|Y_n| + Lambda_n = o_U(|Y_n|)`.
- `(FS_f)` for `psi_n = log f_n(Q_n(y))` is the second half of (FS-groupoid), for the groupoid
  choice fixed in Step 2.

Item 3 gives, for every `c > 1`, that the clusters `i ∉ Bad_n` with `f_n(pi i) < f_n(i)/c` have
weight `o_U(1)`. Together with the upper bound of Step 3, the ratio `f_n(pi_n i)/f_n(i)`
converges to `1` in component-weight measure on `D_n`. This is K–T equation (4), obtained with
no ambient partition.

## Step 5. The remainder of the main proof

Lines 1201–1361 are imported unchanged. They use (4), Lemmas 4.2 and 4.3, the bisection weight
bound (6) and the compression relation `s L s^-1 <= L`. By the audit, they use no ambient
partition and no (T) of the ambient group. In particular the index step K6 applies: on a set
`E_n` of weight `->_U 1` the isotropy index `k_n(i)/k_n(pi i)` is an integer `< 2`, hence `1`,
and the functor is bijective there. The conclusion of the main proof for the one compressor `s`
is `sigma(s) C sigma(s)^-1 = C`, including the reverse inclusion, which Kun--Thom derive from
the compression relation in the same lines. This is FSK1.

## Step 6. FSK2 and FSK3

*FSK2.* The set `N = {g in G : sigma(g) C sigma(g)^-1 = C}` is a subgroup. By FSK1 it contains
`Comp_G(L)`, so it contains `<Comp_G(L)>`. Let `g in <Comp_G(L)>`, `z in C_G(L)` and `l in L`.
Then `sigma(z) in C`, so `sigma(g z g^-1) in C` commutes with `sigma(l)`, and
`sigma([g z g^-1, l]) = 1`. A sofic representation is injective, since
`tr sigma(h) = 0 != 1 = tr sigma(1)` for `h != 1`. So every generator of `D_G(L)` is trivial, and
`D_G(L)`, their normal closure, is `1`.

*FSK3.* An (EK1) witness has `D_G(L) = K x {0} != 1`, with `G = K semidirect Z` sofic. By FSK2 no
sofic representation of `G`, over any nonprincipal `U`, has `sigma|_L` finite-scale. ∎

## Scope

- Only the two ambient inputs are replaced. Every step that uses property (T) of `L` (Kun's
  decomposition, the Alekseev–Thom groupoid) is imported as is.
- (LOG) variants are not claimed. `lambda_n` depends on the compressor, and the K–T deletions in
  Step 2 are not quantitatively controlled.
- Profile regularization (PR) is not claimed.
