# Degree-one Bernoulli expansion fails across amenable HNN seams

Lane ex3-bernoulli-membrane-failure, 2026-09-13. **Unreviewed.** Predecessor: ex2-rokhlin-almost-cocycle,
`weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md` (Sections 12, 17).

## 0. Summary

- **Theorem A.** Let `Gamma` be an HNN extension of a finitely presented nonamenable group `A_0` over a subgroup
  `C = Z^d` (`d <= 2`). Suppose some `chi in Hom(A_0, Z/2)` is not compatible with the HNN relation, and the
  Bernoulli shift `X = [0,1]^Gamma` is Z/2-cocycle superrigid. Then `X` has **no** degree-one cocycle expansion
  with Z/2 coefficients, at any rate. There are cochains `c_n` with relator defect `-> 0` whose distance to every
  exact cocycle stays above a fixed `theta_0 > 0`.
- **Example.** `Gamma = Z^2 x|_phi F_3` with `phi(t_1) = [[1,2],[0,1]]`, `phi(t_2) = [[1,0],[2,1]]`,
  `phi(t_3) = [[1,1],[0,1]]`. It is finitely presented and w-rigid (`(Gamma, Z^2)` has relative (T)), so Popa's
  theorem applies to `X`. Yet expansion fails. The general principle "w-rigid, finitely presented, hence degree-one
  Bernoulli expansion" is false.
- **Consequence B.** For this `Gamma` there is a free action `Y`, weakly equivalent to `X`, carrying a Z/2-cocycle
  that is not cohomologous to any homomorphism. Z/2-cocycle superrigidity of Bernoulli shifts is **not** an
  invariant of weak equivalence. Equivalently (Theorem U of the predecessor, or directly), superrigidity fails for
  the metric ultrapower.
- **Mechanism.** The cochain is the constant `chi` on `A_0`. The HNN letter carries an approximate eigenfunction of
  the amenable seam `C`. Its defects sit on sparse marker hypersurfaces, the "membranes": one row of `C`-orbits in
  every `~1/q` rows. Popa's untwisting step (weak mixing of the rigid normal subgroup) does not survive the
  ultrapower for amenable `C = Z^2`, and that is exactly the step these cochains exploit.
- **What it does not reach.** The instance `bernoulli-shifts-have-degree-one-cocycle-expansion` for `Sp_4(Z)` stays
  open. `Sp_4(Z)` has (T), hence property FA, hence no HNN or amalgam splitting (Section 8).

## 1. Setting

`Gamma = <S | R>` is finitely presented, `X = [0,1]^Gamma` with product measure `mu` and shift
`(g x)(h) = x(g^-1 h)`. A cochain is a measurable `c : S x X -> Z/2`, extended to words by
`c(s_1...s_k, x) = sum_i c(s_i, s_(i+1)...s_k x)` and `c(s^-1, x) = -c(s, s^-1 x)`.
- Defect: `|delta c|_max = max_(r in R) mu{x : c(r, x) != 0}`.
- Distance to a cocycle: `|c - z|_max = max_(s in S) mu{c(s, .) != z(s, .)}`. `Z^1` is the set of cochains with
  `c(r, .) = 0` a.e. for every `r`; these are exactly the measurable cocycles `Gamma x X -> Z/2`.
- **Degree-one expansion with rate `rho`** (`rho(eps) -> 0`): `dist(c, Z^1) <= rho(|delta c|_max)` for all `c`.
  This is the form in `bernoulli-shifts-have-degree-one-cocycle-expansion`.
- `z` is cohomologous to `chi' in Hom(Gamma, Z/2)` when `z(g, x) = F(gx) - F(x) + chi'(g)` a.e. for a measurable
  `F : X -> Z/2`.

## 2. Theorem A

**Data.**
- `A_0 = <S_0 | R_0>` is finitely presented and nonamenable.
- `C <= A_0` is free abelian of rank `d in {1, 2}`, with basis `c_1, ..., c_d` written as words in `S_0`.
- `theta : C -> A_0` is an injective homomorphism.
- `Gamma = <S_0, t | R_0, t c_k t^-1 = theta(c_k) (k = 1..d)>` is the HNN extension.

**Hypotheses.**
- (H1) There is `chi in Hom(A_0, Z/2)` with `rho := chi o theta - chi|_C != 0` in `Hom(C, Z/2)`.
- (H2) Every measurable cocycle `Gamma x X -> Z/2` is cohomologous to a homomorphism.

**Conclusion.** Let `kappa > 0` be a Kesten constant of `(A_0, S_0)`, i.e.
`sum_(s in S_0) ||lambda(s) xi - xi||^2 >= kappa ||xi||^2` on `l^2(A_0)`, and set
`theta_0 = kappa / (kappa + 4|S_0|)`. For every `delta > 0` there is a cochain `c` on `X` with
`|delta c|_max <= delta` and `dist(c, Z^1) >= theta_0`. So `X` has no degree-one cocycle expansion with Z/2
coefficients.

**Non-extension.** Every `chi' in Hom(Gamma, Z/2)` satisfies `chi'(theta(c)) = chi'(t c t^-1) = chi'(c)`. So by (H1),
no homomorphism of `Gamma` restricts to `chi` on `A_0`.

## 3. Lemma M (markers): approximate eigenfunctions of the seam

**Lemma M.** Let `d in {1,2}`, let `rho : Z^d -> Z/2` be a homomorphism, and let `Z^d` act on `Y = [0,1]^(Z^d)` by
`(u y)(g) = y(g - u)`. For every `delta > 0` there is a measurable `eta : Y -> Z/2` with
`mu{y : eta(c_k y) - eta(y) != rho(c_k)} <= delta` for each basis vector `c_k`.

*Proof.*
1. **Reduction.** If `eta_1, eta_2` are `delta`-approximate eigenfunctions for `rho_1, rho_2`, then `eta_1 + eta_2`
   is `2 delta`-approximate for `rho_1 + rho_2`. So it suffices to treat the coordinate characters `u -> u_k mod 2`,
   and by symmetry `u -> u_d mod 2`.
2. **`d = 1`.** Put a marker at `j` when `y(j) < q`, and let `m(y) = max{j <= 0 : y(j) < q}`, which is finite a.s.
   Set `eta(y) = m(y) mod 2`. Since `(c_1 y)(j) = y(j - 1)`, the marker set shifts up by one, so
   `m(c_1 y) = m(y) + 1` unless `0` is a marker of `y`. The error is `q`; take `q = delta`.
3. **`d = 2`, markers.** Write `g = (i, j)`, rows indexed by `j`. For `N >= 1` let
   `R_j(y) = #{i in [0, N) : y(i, j) < 1/2}`, so `R_j ~ Bin(N, 1/2)`, independent over `j`. Put a marker at `j` when
   `R_j >= r`, with `q := P(R >= r)` and `q' := P(R in {r-1, r})`. Set `m(y) = max{j <= 0 : marker}` and
   `eta(y) = m(y) mod 2`.
4. **Along `c_2`.** `R_j(c_2 y) = R_(j-1)(y)`. As in step 2, the error is at most `q`.
5. **Along `c_1`.** `R_j(c_1 y)` counts `i in [-1, N-1)`, so it differs from `R_j(y)` by at most 1. The marker at `j`
   can flip only if `R_j(y) in {r-1, r}`.
   - If `m(c_1 y) != m(y)`, let `j = max(m(y), m(c_1 y)) <= 0`. The marker status at `j` differs between `y` and
     `c_1 y`, and `y` has no marker in `(j, 0]`.
   - Rows are independent, so the error is at most `sum_(k >= 0) q' (1-q)^k = q'/q`.
6. **Parameters.** Pick `t` with `Phibar(t) = delta/2` and `r_N = ceil(N/2 + t sqrt(N)/2)`.
   - By the CLT, `q_N -> Phibar(t)`, so `q_N <= delta` for large `N`.
   - `q'_N <= 2 max_k P(Bin(N,1/2) = k) <= 2 sqrt(2/(pi N)) (1 + o(1)) -> 0`, so `q'_N / q_N <= delta` for large `N`.
   QED

**Transfer to `X`.** For `C <= Gamma` the restriction `p(x) = x|_C` is a measure-preserving `C`-equivariant map onto
the Bernoulli shift of `C = Z^d`: for `u in C` and `g in C`, `(u x)(g) = x(u^-1 g)`. So `eta o p` is an approximate
eigenfunction on `X` with the same error.

## 4. Lemma S: spectral gap detects characters

**Lemma S.** Let `A_0 <= Gamma` be nonamenable, with finite generating set `S_0` and Kesten constant `kappa`. Let
`F : X -> Z/2` be measurable and `tau in Hom(A_0, Z/2)` nonzero. Then
`max_(s in S_0) mu{F(s x) - F(x) != tau(s)} >= theta_0 = kappa / (kappa + 4|S_0|)`.

*Proof.*
1. **`L^2_0(X)` restricted to `A_0` lies in a multiple of `lambda_(A_0)`.**
   - Take a product basis from an orthonormal basis `{1} u {b_i}` of `L^2[0,1]`. Basis vectors other than `1` are
     indexed by finitely supported `a != 0`, which `Gamma` permutes.
   - The stabilizer of `a` preserves the finite set `supp(a)`, so it lies in `supp(a) supp(a)^-1` and is finite.
   - `l^2(A_0 / K)` for finite `K`, twisted by any character, is induced from a finite subgroup and hence contained
     in `lambda^(+|K|)`. Twisting `lambda` by a character gives `lambda` again.
   - So `sum_s ||pi(s) xi - psi tau(s) xi||^2 >= kappa ||xi||^2` for `xi in L^2_0(X)`, where `psi : Z/2 -> {+-1}` is
     the nontrivial character and `pi(g) xi = xi o g^-1`.
2. **Estimate.** Suppose the maximum is `<= delta`. Then `Phi = psi o F` satisfies
   `||pi(s) Phi - psi tau(s) Phi||^2 <= 4 delta`: substitute `x -> s^-1 x`, and note `-tau = tau`.
3. **Split.** Write `Phi = m 1 + Phi_0`. The constant and `L^2_0` parts of `pi(s)Phi - psi tau(s)Phi` are
   orthogonal, so:
   - summing over `s`, `kappa ||Phi_0||^2 <= 4 |S_0| delta`;
   - at `s_0 in S_0` with `tau(s_0) = 1`, which exists because `S_0` generates, `4 |m|^2 <= 4 delta`.
4. **Conclusion.** `1 = |m|^2 + ||Phi_0||^2 <= delta (1 + 4|S_0|/kappa)`. QED

The Kesten constant exists because `A_0` is nonamenable: by Hulanicki's theorem, `lambda_(A_0)` has almost
invariant vectors iff `A_0` is amenable. This is a textbook fact, recalled and not re-read.

## 5. Proof of Theorem A

1. **The cochain.** `c(s, x) = chi(s)` for `s in S_0`, and `c(t, x) = eta(x)`, with `eta` from Lemma M for
   `rho = chi o theta - chi|_C`, transferred to `X`, error `delta`.
2. **Relators in `R_0`.** `c(r, x) = chi(r) = 0`, because `chi` is a homomorphism.
3. **HNN relators.** Let `r_k = t V t^-1 W^-1` with `V = c_k` and `W = theta(c_k)` words in `S_0`. With
   `u = t^-1 W^-1 x`:
   `c(r_k, x) = eta(c_k u) + chi(c_k) - eta(u) - chi(theta(c_k)) = [eta(c_k u) - eta(u)] - rho(c_k)`.
   The map `x -> u` preserves `mu`, so the defect is at most `delta`.
4. **Distance.** Let `z in Z^1` with `|c - z|_max <= delta'`. By (H2), `z(g, x) = F(gx) - F(x) + chi'(g)`.
   - For `s in S_0`, `mu{F(sx) - F(x) != tau(s)} <= delta'` with `tau = chi - chi'|_(A_0)`.
   - `tau != 0` by non-extension, so Lemma S gives `delta' >= theta_0`. QED

## 6. The example `Gamma = Z^2 x| F_3`

1. **Presentation.** `S_0 = {e_1, e_2, t_1, t_2}` and `R_0 = {[e_1, e_2], t_i e_j t_i^-1 = phi(t_i)(e_j)}`. Here
   `phi(t_1)` fixes `e_1` and sends `e_2 -> 2e_1 + e_2`, and `phi(t_2)` sends `e_1 -> e_1 + 2e_2` and fixes `e_2`.
   Then `A_0 = Z^2 x| F(t_1, t_2)`. Take `C = <e_1, e_2>` and `theta = phi(t_3)`, which fixes `e_1` and sends
   `e_2 -> e_1 + e_2`. The HNN extension is `Gamma = Z^2 x| F(t_1, t_2, t_3)`, finitely presented and torsion-free.
2. **(H1).** Set `chi(e_1) = 1` and `chi(e_2) = chi(t_i) = 0`.
   - `chi` respects `R_0`: `chi(2e_1 + e_2) = 0 = chi(e_2)` and `chi(e_1 + 2e_2) = 1 = chi(e_1)`.
   - `rho(e_2) = chi(e_1 + e_2) - chi(e_2) = 1`.
   - Every homomorphism of `Gamma` kills `e_1`, because `chi'(e_1 + e_2) = chi'(e_2)`.
3. **Nonamenable.** `A_0` contains `F(t_1, t_2)`, and `|S_0| = 4`, so `theta_0 = kappa/(kappa + 16)`.
4. **(H2) via Popa.** `popa-bernoulli-cocycle-superrigidity` needs an infinite normal subgroup `H` with
   `(Gamma, H)` relatively (T) and the shift weakly mixing on `H`. Take `H = Z^2`: the shift restricted to an
   infinite subgroup is mixing.
5. **Relative (T) for `(Gamma, Z^2)`.**
   - **(a)** `(Z^2 x| SL_2(Z), Z^2)` has relative (T): `elementary-linear-semidir-pair-relative-t` with `R = Z`,
     since `EL_2(Z) = SL_2(Z)`.
   - **(b)** Sanov: `<[[1,2],[0,1]], [[1,0],[2,1]]>` is free on these generators and of finite index 12 in
     `SL_2(Z)` (recalled, not re-read; the same fact is used in `affine-sl2z-purely-matricial-field-proof`). So
     `A_0` is a finite-index subgroup of `Z^2 x| SL_2(Z)` containing `Z^2`.
   - **(c) Lemma FI.** If `(G, N)` has relative (T), `N` is normal and `N <= G_1 <= G` with `[G : G_1]` finite,
     then `(G_1, N)` has relative (T).
     - Let `sigma` be a representation of `G_1` with almost invariant vectors. Take coset representatives
       `x_1..x_m` and put `f(x_i g) = sigma(g)^-1 xi / sqrt(m)` in `Ind sigma`.
     - For `y in G`, `y^-1 x_i = x_j g'` with `g'` in a finite set, so `||lambda(y) f - f||^2 <= max ||sigma(g') xi - xi||^2`.
       Hence `Ind sigma` has almost invariant vectors, and relative (T) gives a nonzero `N`-invariant `f`.
     - If `f(x) != 0`, then `f(x) = f(n^-1 x) = sigma(x^-1 n x) f(x)` for all `n in N`, and `x^-1 N x = N`. So
       `f(x)` is a nonzero `N`-invariant vector of `sigma`.
   - **(d) Lemma UP.** If `A_0 <= Gamma` and `(A_0, N)` has relative (T), then so does `(Gamma, N)`: restrict to
     `A_0`.
6. **Conclusion.** Theorem A applies: the Bernoulli shift of `Gamma` has no degree-one cocycle expansion with Z/2
   coefficients, although it is Z/2-cocycle superrigid.

## 7. Consequences

**B (weak equivalence).**
- **Statement.** For `Gamma` of Section 6 there is a free p.m.p. action `Y`, weakly equivalent to `X`, and a
  measurable cocycle `w : Gamma x Y -> Z/2` not cohomologous to any homomorphism.
- **Construction.** Let `c_n` be the cochains of Theorem A with defects `delta_n -> 0`. On the Loeb ultrapower `L`
  of `X`, `w(s, [x_n]) = [c_n(s, x_n)]` has Loeb-null relator defects, so it is a cocycle.
  - `Y` is a standard model of the separable invariant factor of `L` generated by the sets `{w(s, .) = 1}` and the
    diagonal copy of `X`.
  - `Y` has `X` as a factor, so it is free, and by `abert-weiss-free-actions-weakly-contain-bernoulli`, `X ≺ Y`.
  - `Y ≺ X`: any finite configuration of Loeb sets is approximated by internal sets, whose joint translate measures
    are `U`-limits of those in `X`. This is the easy half of Conley–Kechris–Tucker-Drob.
- **Why `w` is not cohomologous to a homomorphism.** Suppose `w = delta F + chi'` on `Y`, hence on `L`.
  - `F` is `U`-a.e. an internal `[F_n]`, so `mu{F_n(sx) - F_n(x) != chi(s) - chi'(s)} -> 0` along `U` for
    `s in S_0`.
  - This contradicts Lemma S, as `chi - chi'|_(A_0) != 0`.
- **Contrast.** `X` itself is Z/2-cocycle superrigid by Popa. The same argument, with the metric ultrapower
  algebra, shows directly that statement (ii) of `bernoulli-expansion-iff-ultrapower-cocycle-superrigidity` fails
  for `Gamma`.

**C (firewall for proofs of expansion).**
- **Popa's hypotheses are not enough.** Any argument that degree-one Bernoulli expansion (or ultrapower
  superrigidity) holds must fail on `Z^2 x| F_3`, so it must use more than Popa's hypotheses plus finite
  presentation.
- **The failing step.** Popa's untwisting over the normalizer uses weak mixing of the rigid normal subgroup. For
  amenable `Z^2`, the ultrapower acquires eigenfunctions for every character (Lemma M), so that step fails there.
- **Candidate inputs.** Candidate extra inputs are nonamenability of the rigid w-normal subgroup (for then weak
  mixing does survive ultrapowers, by the Lemma S estimate), or property (T) of `Gamma` itself (which also rules
  out HNN seams).

## 8. Where it stops for `Sp_4(Z)`

- **No splitting.** `Sp_4(Z)` has (T), so it has property FA and no HNN or amalgam decomposition. Theorem A has
  nothing to act on.
- **General form.** The underlying mechanism works whenever `c` is the constant `chi_H` on some nonamenable
  `H <= Gamma`, `chi_H` does not extend to `Gamma`, and the curvature can be absorbed by approximate eigenfunctions
  of amenable subgroups. The direct proof then goes through with Lemma S.
- **Obstacle.** In `Sp_4(Z)`, a long-root generator `x_(2e_1)` commutes with the `SL_2(Z)` generated by
  `x_(+-2e_2)`, which is nonamenable. On such relators Lemma S forces the absorbing function to be nearly constant.
  Short-root generators commute only with an amenable `Z^2`, but their Steinberg commutator relations couple them
  to long roots. Whether all curvature can be routed through amenable seams is **not decided here**.

## 9. Model tests

- **Hypothesis (H1) necessary.** If `rho = 0` (e.g. `chi(e_1) = 0`), the constant `chi` extends and `c = chi` is an
  exact cocycle, so no failure.
- **Hypothesis (H2) necessary for the distance bound.** Without superrigidity other exact cocycles can sit near
  `c`. For the free product `A_0 * Z`, the cochain `c = chi` on `S_0`, arbitrary on the free letter, is itself an
  exact cocycle.
- **Seam must be amenable.** If `C` is nonamenable, Lemma S forbids approximate eigenfunctions for `rho != 0`, and
  the construction dies. This is consistent with Section 8.
- **Exact level.** `c` is never exact: on `X`, an exact cocycle equal to `chi` on `S_0` would contradict Popa plus
  Lemma S. The failure is an ultrapower phenomenon, as required.

## 10. Trust surface

- **Recalled, not re-read:**
  - Hulanicki–Kesten, existence of `kappa`;
  - Sanov's free subgroup and its finite index;
  - Loeb measure approximation by internal sets;
  - the easy half of Conley–Kechris–Tucker-Drob.
- **Imported through repo nodes:** Popa Theorem 0.1 (`popa-bernoulli-cocycle-superrigidity`), relative (T) for
  `(EL_2(R) x| R^2, R^2)`, Abért–Weiss.
- **Novelty not checked.** WebSearch budget exhausted and arXiv API rate-limited (HTTP 429, empty reply from MSI).
  Folklore status of "superrigidity is not a weak-equivalence invariant" is unknown to this lane.
