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
