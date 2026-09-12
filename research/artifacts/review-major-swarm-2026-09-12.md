# Adversarial review: major-problems swarm, established claims (2026-09-12)

Lane `major-reviewer`. Each section gives a verdict (PASS, FAIL or GAP) for one
established claim, what was checked line by line, and the trust surfaces that
were not re-derived. Reviewed at tip `7a6f30fee`.

## 1. `commutant-excess-bounded-by-aspect-ratio-jump-mass` (11b4ec3e2) — PASS

Checked:
- `z_i` (isotypic projections of `pi`) lie in `A <= B`, and `w_j` lie in the centre
  of `B`, so they commute. `H_ij = C^(m_i) (x) C^(c_ij) (x) W_j` is their joint range.
- `R_ij = m'_j d_i/(m_i e_j) >= c_ij^2 >= 1`, from `m'_j >= m_i c_ij` and
  `d_i >= c_ij e_j`.
- Low pairs (`R_ij < 1+c`, `c < 1`) force `c_ij = 1`, `m'_j - m_i < c m_i` and
  `d_i - e_j < c e_j`.
- **Matching, presentation slip.** For two low partners `i != i'` of one `j`, the proof
  writes "would give `m_i + m_(i') > m'_j`", which is not the right inequality. The
  correct argument: low `(i,j)` gives `m_(i') <= m'_j - m_i < c m_i`, and low `(i',j)`
  gives `m_i < c m_(i')`, so `m_i < c^2 m_i`, impossible. The conclusion stands.
- `E_A x = sum_i y_i (x) 1_(V_i)` with `y_i = d_i^(-1) sum_(j') e_(j') Tr(x_(j')^(i,i))`,
  since `x` is block diagonal in `j`. On a low pair the operator-norm defect is at most
  `2(d_i - e_j)/d_i < 2c`, and summing `m_i e_j <= n` gives `||P(x - E_A x)P||_2 <= 2c`.
- The corner terms contribute `2 tau(1-P)^(1/2)` each, since `||x - E_A x|| <= 2`.

Trust surfaces: none beyond Schur's lemma.

## 2. `vertex-rounding-reduces-ccr-to-commutant-excess` (11b4ec3e2) — PASS

Checked against artifact `hs-scale-pinning-2026-09-12.md` Section 2:
- **Item 1.** Kazhdan's inequality applied to `Ad pi_n` on `L^2(M_(n'))` with fixed space
  `A_n`; commutation on generators suffices because `sigma` is asymptotically
  multiplicative. For `Lambda`, `(t F t^(-1), kappa)` is a Kazhdan pair, and each
  `t s t^(-1)` is a fixed word in `F`.
- **Item 2.** The (=>) direction uses that `E_(A_n)` is the 2-norm nearest point in `A_n`.
- **Item 3.** `w` is almost invariant under `Ad(pi_n (+) pi~_n)`; its expectation `y` is a
  contraction; the corner `x = e_22 y e_11` intertwines. The polar estimate
  `||v - x||_2 <= ||1 - |x| ||_2 <= tau(1 - x^* x)^(1/2)` uses `(1-a)^2 <= 1-a^2` on `[0,1]`.
- **Item 4.** `|F_a(lambda x) - F_a(x)| <= (1/4) log lambda` holds because
  `F_a = 1/(1 + a e^(-u))` has derivative at most `1/4` in `u = log x`.

Notes:
- The artifact bounds the low-multiplicity types only on the `pi_n|Lambda` side. The
  symmetric bound on the `pi~_n` side, multiplicities `m~_j` against `r_j`, is needed
  too. It is the same estimate with `tau(1 - v v^*) = tau(1 - v^* v)`.
- In the "Reading" example (an irreducible splitting into two halves) the excess is `1`,
  attained at `x = 2p - 1`, not `1/2`. The point, a macroscopic excess against additive
  `L^1` distance `1/n`, is unaffected.

Trust surfaces: (H1) itself is the open hypothesis; nothing else external.

## 3. `relative-defect-iff-surjective-compressor-endomorphisms` (f0715d2aa) — PASS

Checked:
- Commutator identities with `[a,b] = a b a^(-1) b^(-1)`:
  `[z_1 z_2, gamma] = z_1 [z_2,gamma] z_1^(-1) [z_1,gamma]`,
  `[z^(-1),gamma] = z^(-1)[z,gamma]^(-1) z`, and
  `[t^(-1) z t, gamma] = t^(-1) [z, t gamma t^(-1)] t`.
- `z Gamma z^(-1) <= M Gamma = Gamma` uses `M <= Gamma`.
- The sofic input (step 4) makes `G` normalize `C_H(Gamma)`, so `t^(-1) K t = K` for
  `t in P_Gamma <= G`. `eps_t` is well defined and injective.
- Surjectivity of `eps_t` iff `t Z t^(-1) = Z`, via `Z <= (t^(-1) Z t) K <= t^(-1) Z t`.
- `G` normalizes `Z` iff every `t in P_Gamma` does, because `t Z t^(-1) = Z` also gives
  the inverse; `P_Gamma` generates `G` by infranormality.
- Instances: in `SL_3(Z) semidirect <alpha>` the centralizer is trivial because `alpha`
  is outer and `SL_3(Z)` is centreless, so `Q = Z/2`. For the Leavitt cover `eps_(u_hat)` is
  well defined unconditionally, since `K = N` is normal.

Trust surfaces:
- `sofic-groups-kill-rigid-compression-defects` (reviewer PASS; rests on Kun--Thom
  Theorem 4.1, unrefereed v3);
- torsion-freeness of the cover and Theorem 3(c) of the cover artifact, for the instance
  only.

## 4. `hs-literal-commutant-profile-rounding-is-false` (4d8097c38) — PASS

Checked:
- The finite-quotient gap: for `xi` orthogonal to `pi(Gamma)'`, the average of
  `||pi(g)xi - xi||^2` over `Q` equals `2||xi||^2`. The maximum is attained on `F`
  because `q(F) = Q`.
- `[p, E(x)] = 0` because `p` is central in `C I_d (+) M_d`, and `||[p,y]||_2 <= ||y||_2`
  by the corner decomposition.
- (R1)-(R4) follow from `||U_s - pi(s)||_op < eta` and the density of irreducible tuples.
- The consequence matches the crux as stated: rounding to central projections of the
  literal commutant `sigma_n(Gamma)' cap M_n`. Since `eps = O(delta)`, no `f -> 0` exists,
  already in fixed dimension.

Trust surfaces: density of irreducible unitary tuples (standard), cited from
`regular-quotient-perturbation-defeats-literal-poincare`.

## 5. `flexible-hs-stability-passes-to-kazhdan-kernel-quotients` (81678a0ab) — PASS

Checked:
- Step 1: a unitary `u` with `||u^2 - u||_2 -> 0` has `||u - 1||_2 -> 0`, so `sigma_n(1) ~ 1`.
- Step 3: `||(1-P)rho(g)P||_HS^2 = d_n - ||P rho(g) P||_HS^2 = o(d_n)`.
- Step 5: Kazhdan's inequality on the complement of the `rho_n(N)`-fixed space, summed over
  a basis of `V_n`.
- Step 6: `E_n H_n` is `rho_n(Gamma)`-invariant because `N` is normal.
- Step 7:
  - `dim ker(E_n P) <= ||(1-E_n)P||_HS^2`;
  - `J` is an isometry because the ranges `E_n H_n` and `C^(m_n)` are orthogonal;
  - `||J - T||_HS^2 <= || |T| - P ||_HS^2 + m_n`, a bound that counts `ker T` twice but
    stays valid.
- Step 8: `J^* lambda_n J = J^* R J`, and `||J^* R J - iota^* R iota||_HS <= 2||J - iota||_HS`.

Note: if Dogon--Vigdorovich's definition also requires `D_n/d_n -> 1`, the proof still
works. `dim E_n H_n + m_n <= D_n + o(d_n)`.

Trust surfaces: the exact wording of Dogon--Vigdorovich Definition 1.2. The extracted
text on MSI (`review-lit/dv.txt`) did not return the definition, and the argument is
robust to the ratio variant.

## 6. `flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear` (88878e9e7) — PASS

The chain is:
- stability of `Gamma/N`;
- `hyperlinear-flexibly-hs-stable-group-is-residually-finite`: finitely generated
  maximally almost periodic groups are residually finite by Malcev applied to each
  finite-dimensional image;
- an infinite residually finite group has a nontrivial finite-dimensional representation.

Correct as stated.

## 7. `classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan` (c2c479926) — PASS

The main implication is correct:
- Belegradek--Osin needs `Q` finitely presented and `H` non-elementary hyperbolic;
- `N` has (T) as a quotient of `H`;
- (T) is closed under extensions;
- stability then descends by section 5.

Trust surface in a consequence line, not in the theorem: "the binary Leavitt unit group has
property (T)", derived from `binary-leavitt-unit-group-has-tt-mod-t` plus perfectness.
That derivation (every quasi-cocycle into a representation without invariant vectors is
bounded, and `Hom(L^x, R) = 0`) was not re-derived here.

## 8. `euler-integral-measure-violates-serre-inequality` (2512ebda0) — PASS

Checked numerically and analytically:
- **The density of `XY`.** It is `(2/pi^2) int_(|u|/2)^2 dx/sqrt((4-x^2)(4x^2-u^2))`. The
  bounds `4-x^2 <= 4(2-x)` and `4x^2-u^2 <= 16(x-|u|/2)` give `f_2 >= 1/(4 pi)`.
- **The antiderivative.** `d/dz[-(1/2) log((2+sqrt(4-z^2))/z)] = 1/(z sqrt(4-z^2))`
  (verified). `int_(3/2)^2 = (1/2) log(2.2153) = 0.3977`, so `f_nu >= 0.02014` on
  `[-6,6]`.
- **Young and Hölder.** `||f_1||_(3/2)^(3/2) = pi^(-3/2) 2 . 4^(-3/4) B(1/4,1/2) = 0.66594`
  (recomputed: `B(1/4,1/2) = 5.2441`), so `||f_sigma||_inf <= 0.44348`. Then
  `23 x 0.02014 = 0.463 > 0.4435`, `mu >= 0`, and the mass is `22`.
- **Mahler measures.** `m((x+1/x)(y+1/y)(z+1/z)) = 3 m(x^2+1) = 0`. Jensen in `z` gives
  `m(x+1/x+y+1/y+z+1/z) > 0`, from the event `|c| > 2`.
- **The hypothesis.** It matches the refuted node's original statement: finite positive
  measure on a compact interval, integer moments including `m_0 = 22`, and integral
  exponential series. `1 + zZ[[z]]` is a multiplicative group, so `F_Q(mu) =
  F_Q(nu)^23 F_Q(sigma)^(-1)`.

Trust surface: `torsion-free-integral-zeta-is-an-integer-euler-product`, not re-derived
here. Sanity check for `Z`: `exp(sum C(2k,k) z^(2k)/(2k))` is the Catalan series, which
is integral.

## 9. bs-pc-pu fibre-summation claims (ca5fb82d2, e76d838dd)

Hutchcroft arXiv:1804.10191 was extracted on MSI (`gs txtwrite`), and the cited
statements were read:
- **Corollary 2.6:**
  `||T_p||_(q->q) >= (1-p)/(||A||_(q->q) (p_(q->q) - p))`.
- **Lemma 2.8:** `chi_p(1 - iota) <= ||T_p||_(2->2) <= chi_p sqrt(1 - iota^2)`, for
  symmetric substochastic normalizations.
- **Proposition 4.1:** the magic lemma, with one or two half-spaces.
- **Corollary 4.3:** supporting half-spaces for finite **connected** sets.
- **Proposition 5.1 and Lemma 5.3:** `limsup (p_c - p) chi_p < infinity` for unimodular
  quasi-transitive nonamenable hyperbolic graphs.

### 9a. `fpbs-fibre-summed-connectivity-operator` — PASS

- **Schur's test.** Row and column sums of the block `(q, q')` equal `sigma_p(q^(-1)q')`
  by normality and symmetry.
- **Equality for amenable `H`.** Weak containment `Ind 1_H <= lambda_Gamma`, applied on
  finitely supported truncations, with monotone limits.
- **Note.** The sentence "Hutchcroft's L2 condition holds iff `S_(p_c)` is bounded" needs
  `H` amenable in the (=>) direction. In the node it follows the amenable case, but it
  reads as unconditional.

### 9b. `fpbs-fibre-bubble-forces-mean-field-susceptibility` — PASS

Checked:
- **Lemma 2.2.** The mass transport `E sum_q m(q)^2 = E[|K_o||K_o ∩ H|]`, the tree-graph
  bound `chi_p B`, and the heavy/light split.
- **Lemma 2.3.** Mass transport plus the union bound over `N_r` choices of `b`.
- **Where Corollary 4.3 enters.** It needs connected sets. The application is to `pi(K_o)`,
  which is connected in `Cay(Q, pi(S) \ {1})` because `K_o` is connected. The artifact's
  (H1) omits the word "connected", but the use is valid.
- **Independence.** The events are measurable with respect to edges with an endpoint in
  `H` or in `gamma H`, and these sets are at distance at least 2.

Trust surfaces: the finite-energy step (5.4) and Russo (5.2) of Hutchcroft's Proposition
5.1, and his Lemma 3.6 on separated translates, were not re-derived. The statement of
Lemma 3.6 was not located in the extraction.

### 9c. `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap` — PASS

Checked:
- `S_p/chi_p` is symmetric and stochastic, and `1 - iota` is defined as in Hutchcroft's
  Cheeger constant.
- The magic-lemma bound per `a in A'`: at most `N(eps)` exceptional cosets, each
  `<= max sigma <= B^(1/2)`, plus at most two far half-spaces, each `<= sh(1/eps) chi_p`.
- `1 - iota^2 <= 2(1 - iota)`.
- If `p_(2->2) = p_c`, Corollary 2.6 forces `(p_c - p)||T_p|| >= (1-p)/||A||`, which
  contradicts `(p_c - p)||T_p|| -> 0`. The artifact's `d` bounds `||A||` from above, so
  the direction is right.

### 9d. `fpbs-relative-susceptibility-tube-excursion-bound` — PASS

- **Tube term.** Blocking levels `2L` apart independently, with probability at least
  `(1-p)^(M_r)` each.
- **Excursion term.** The first exit vertex splits a simple open path into edge-disjoint
  witnesses, so BK applies. The fibre sum gives `sum sigma(q) sigma(q^(-1))`.

### 9e. `fpbs-tree-projected-sphere-bubble-l2-equivalence` — GAP (minor, fillable)

Checked:
- (=>): `sum_R b_R(p_c) = ||S_(p_c) delta_1||^2 <= ||T_(p_c)||^2`, using amenable `H`.
- (<=): left-continuity of `sigma_p(q)`, the tube bound, and cut-set submultiplicativity
  `sigma(wu) <= sigma(w) sigma(u)` for reduced `wu`, proved by BK at a vertex of the
  fibre over `w`. Hence `b_(R+R') <= b_R b_(R')`.

Two steps are asserted but not written:
1. **Uniform boundedness of `b_j(p)` for `j < R_0` and `p < p_c`.** Geometric decay needs
   it to turn `b_(R_0) <= 1 - eta` into `sup_p sum_R b_R < infinity`. Fill: by insertion
   tolerance and FKG, `P_p(o <-> x) <= p^(-c j) P_p(o <-> h(x))` for `x` in a fibre at
   quotient distance `j`, with `h(x) in H` at bounded distance and bounded
   multiplicity. So `sigma_p(q) <= C_j p^(-cj) chi^H_p`, which is bounded on
   `[p_c/2, p_c)` by step 2.
2. **Far half-spaces pull back into boundedly many branches.** It needs a bound, uniform
   in `D`, on the number of depth-`~D/lambda` branches of the tree whose images meet a
   half-space at distance `D` from `Phi(a)`. This is plausible from the visual-size
   comparison for a rough similarity into `H^d`, but it is not proved.

Neither step looks wrong. The claim reads ESTABLISHED, and the open targets downstream
(`fpbs-tree-projected-cayley-graphs-strict-thresholds`) stay OPEN, so no false root is
affected. The owning lanes `bs-pc-pu` and `bs-pc-pu-2` have finished, so no message was
sent.

## Summary

| claim | verdict |
|---|---|
| commutant-excess-bounded-by-aspect-ratio-jump-mass | PASS |
| vertex-rounding-reduces-ccr-to-commutant-excess | PASS |
| relative-defect-iff-surjective-compressor-endomorphisms | PASS |
| hs-literal-commutant-profile-rounding-is-false | PASS |
| flexible-hs-stability-passes-to-kazhdan-kernel-quotients | PASS |
| flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear | PASS |
| classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan | PASS |
| euler-integral-measure-violates-serre-inequality | PASS |
| fpbs-fibre-summed-connectivity-operator | PASS |
| fpbs-fibre-bubble-forces-mean-field-susceptibility | PASS |
| fpbs-hyperbolic-quotient-fibre-estimates-l2-gap | PASS |
| fpbs-relative-susceptibility-tube-excursion-bound | PASS |
| fpbs-tree-projected-sphere-bubble-l2-equivalence | GAP (two unwritten routine steps) |

No FAIL. No graph correction needed.
