---
rg: 2
id: deligne-third-floor-no-polynomial-certificate-proof
kind: route
title: Integrality forces finite point support by Bonami's inequality, and leafwise exactness then kills every polynomial certificate for the Deligne third floor
target: deligne-third-floor-has-no-polynomial-certificate
requires:
  - deligne-third-floor-has-no-character-certificate
  - deligne-opnorm-monomial-models-are-almost-flat-circle-bundles
  - finitely-generated-linear-groups-are-residually-finite
---

Notation of the target. `e(t) = exp(2 pi i t)`. Throughout, `l_max` is the longest relator length of the fixed
presentation, and a "cell" is a 2-cell of `Y`, or of `Y_X`.

## Step 0. Polynomial phases lift to polynomials

Let `Q : E -> T` be continuous with `Delta^(k+1) Q = 0` and `Q|L = 0`.
- `E` is a Banach space, so it is contractible, and `Q` lifts to a continuous `P : E -> R`.
- The function `(y, h_1, ..., h_(k+1)) |-> Delta_(h_1) ... Delta_(h_(k+1)) P (y)` is continuous and `Z`-valued on the
  connected space `E^(k+2)`. It is `0` at `h = 0`, so it is identically `0`.
- By the Mazur-Orlicz theorem, `P = sum_(j<=k) A_j(y, ..., y)` with `A_j` symmetric and `j`-additive. Each `A_j` is a
  fixed finite-difference combination of values of `P` (polarization), so it is continuous, hence `R`-multilinear
  and bounded.
- `Q|L = 0` gives `P(L) subset Z`.

So item 2 for phases follows from item 2 for polynomials.

## Step 1. Denominators of integral polynomials

Let `P = sum_(j<=k) A_j` be continuous with `P(L) subset Z`. Put `N_k = lcm(1, ..., k)`.

**Claim.** For `l_1, ..., l_j in C(Omega, Z)`, we have `j! A_j(l_1, ..., l_j) in N_k^(-j) Z`.

*Proof.*
- `C(Omega, Z) subset L`, so `p(n) = P(n_1 l_1 + ... + n_j l_j)` is an integer-valued polynomial on `Z^j` of degree
  `<= k`.
- Hence `p` is a `Z`-combination of products `prod_i binom(n_i, a_i)` with `sum a_i <= k`.
- The coefficient of the monomial `n_1 n_2 ... n_j` in `p` is exactly `j! A_j(l_1, ..., l_j)`. The forms `A_(j')`
  with `j' != j` are homogeneous of degree `j'` in `n`, so they do not contribute.
- In the binomial basis, only the terms with all `a_i >= 1` contribute. The coefficient of `n` in `binom(n, a)` is
  `(-1)^(a-1)/a`, whose denominator divides `N_k`. QED.

## Step 2. The finite-support lemma (item 1)

Let `A` be a bounded `j`-linear form on `C(Omega)` with `|A(f_1, ..., f_j)| <= b prod ||f_i||`. Assume `M A` is
integer-valued on `j`-tuples of indicators of clopen sets, for some integer `M >= 1`.

**(a) A uniform bound on array support.** Let `U_1, ..., U_m` be a clopen partition of `Omega`, and put
`a(i_1, ..., i_j) = M A(1_(U_(i_1)), ..., 1_(U_(i_j)))`, which lies in `Z`.
- Take independent Rademacher vectors `eps^(1), ..., eps^(j)` in `{+1, -1}^m`, and set
  `S = sum a(i) eps^(1)_(i_1) ... eps^(j)_(i_j)`.
- Then `S = M A(g_1, ..., g_j)` with `g_s = sum_i eps^(s)_i 1_(U_i)` and `||g_s|| = 1`. So `|S| <= M b` pointwise.
- `S` is a multilinear polynomial of degree `j` in independent signs, with `E S^2 = sum a(i)^2`.
- Bonami's hypercontractive inequality gives `||S||_4 <= 3^(j/2) ||S||_2`. Hölder gives
  `||S||_2^3 <= ||S||_1 ||S||_4^2`. Together, `||S||_2 <= 9^(j/2) ||S||_1 <= 9^(j/2) M b`.
- The entries `a(i)` are integers, so the number of nonzero entries is at most
  `sum a(i)^2 <= 9^j M^2 b^2 =: r`.

The bound `r` does not depend on the partition. Call a cell `U_i` *active* if it occurs in some index `i` with
`a(i) != 0`. There are at most `j r` active cells.

**(b) Passing to the limit.**
- Fix a metric on `Omega` and clopen partitions `P_n` with mesh tending to `0`. For each `n`, choose one point in each
  active cell of `P_n`; this gives a set `F_n` with `|F_n| <= j r`.
- Pass to a subsequence along which `F_n` converges in the Hausdorff metric. The limit `F` has `|F| <= j r`.

**(c) Vanishing near `F`.**
- Let `V` be a clopen neighbourhood of `F`, and suppose `f_1 = 0` on `V`.
- `V` contains the `2 delta`-neighbourhood of `F` for some `delta > 0`, and `dist(V, Omega \ V) > 0`.
- For large `n` in the subsequence, every cell of `P_n` lies inside `V` or inside its complement, every active cell
  lies within `delta + mesh(P_n)` of `F`, and so every active cell lies in `V`.
- Let `f^n_s = sum_(U in P_n) f_s(x_U) 1_U` be step approximations. By uniform continuity,
  `||f_s - f^n_s|| -> 0`.
- `A(f^n_1, ..., f^n_j) = M^(-1) sum a(i) prod_s f_s(x_(U_(i_s)))`. Every nonzero term has `U_(i_1)` active, so
  inside `V`, where `f_1 = 0`. So this sum is `0`.
- Boundedness of `A` gives `A(f_1, ..., f_j) = lim A(f^n_1, ..., f^n_j) = 0`.
- The same argument works in any slot.

**(d) Vanishing on `F`.**
- Suppose `f_1 = 0` on `F`. Given `eta > 0`, choose a clopen `V`, containing `F`, on which `|f_1| < eta`. This is
  possible because `Omega` is totally disconnected.
- `f'_1 = f_1 1_(Omega \ V)` is continuous, vanishes on `V`, and has `||f_1 - f'_1|| <= eta`.
- So `|A(f_1, ...)| <= b eta prod_(s>1) ||f_s||`, for every `eta`. Hence `A(f_1, ...) = 0`.

**(e) Conclusion.** By multilinearity, `A(f) - A(g)` telescopes into terms with one slot `f_s - g_s`. If `f|F = g|F`,
each such slot vanishes on `F`. So `A` depends only on the restrictions to `F`. This proves item 1.

**Consequence.** By Step 1, `M = N_k^j j!` works for `A_j`. So every continuous `P` with `P(L) subset Z` has a finite
set `F_P subset Omega`, the union of the sets for `A_1, ..., A_k`, such that `P(y) = P(y')` whenever
`y|F_P = y'|F_P`.

## Step 3. Leafwise exactness on finitely many leaves (item 2)

Let `P` be as in Step 2, with finite support set `F = F_P`. Fix `m in L`.
- The points of `F` are pairs `(c_i, x_i)`, with `x_i` in finitely many `Gamma`-orbits `O` of `G`.
- By the leaf decomposition in Step 3 of `deligne-third-floor-no-character-certificate-proof`, the value
  `(delta theta)(c, x)` involves only the values `theta(s, x')` on finitely many edges, with `x'` in `Gamma x`. Let
  `T` be the finite set of edge-point pairs `(s, x')` that occur for the cells of `F`.
- On each leaf `O`, the leafwise-exactness paragraph of that route (Step 4) gives an integral 1-cochain `beta_O` with
  `delta beta_O = kappa` on `O`, which is a copy of `Y~`.
- `T` is a finite subset of `S x G`, and `G` is totally disconnected. So there is a locally constant, hence
  continuous, `theta in C^1(Y; C(G,R))` with `theta(s, x') = beta_O(s, x')/3` on `T`.
- Then `l = delta theta` is in `L` and `l|F = kappa/3|F`.
- So `(kappa/3 + m)|F = (l + m)|F`, and `P(kappa/3 + m) = P(l + m)`, which lies in `Z` because `l + m` is in `L`.

With Step 0 this proves item 2. ∎(2)

## Step 4. Countable sets (item 3)

Let `D = {d_1, d_2, ...}` be a countable subset of `Omega`, and put `F_n = {d_1, ..., d_n}`.
- Step 3 gives a continuous `theta_n` with `delta theta_n = kappa/3` on `F_n`. Put `w_n = delta theta_n - kappa/3`,
  a continuous function that vanishes on `F_n`.
- Choose a clopen partition on whose cells `w_n` oscillates by less than `1/n`. Define `m_n in C(Omega, Z)` to be `0`
  on the cells that meet `F_n`, and `round(w_n(x_U))` on each other cell `U`, for some sample point `x_U` of `U`.
- Then `y_n = m_n - w_n = kappa/3 + (m_n - delta theta_n)` lies in `kappa/3 + L`. It satisfies
  `||y_n|| <= 1/2 + 1/n` and `y_n|F_n = 0`.
- If `Phi` is `L`-invariant, then `Phi(y_n) = Phi(kappa/3)`. If also `y_n -> 0` boundedly and pointwise on `D`
  forces `Phi(y_n) -> Phi(0)`, then `Phi(kappa/3) = Phi(0)`.
- This class includes every `L`-invariant cylinder function, i.e. every function `phi(y|F')` with `phi` continuous
  on `R^(F')` and `F'` finite, that is constant on the cosets `y + L`. It includes the characters trivial on `L`, whose Riesz measures are finitely
  atomic.
- Item 2 is **not** a special case of item 3. A polynomial with `P(L) subset Z` need not be `L`-invariant modulo `Z`:
  for example, `(y + 1)^2 - y^2 = 2y + 1`. Item 2 needs Step 3 applied to `kappa/3 + m` directly. ∎(3)

Remark: `dist(., cl L)` is `L`-invariant and continuous for the sup norm. If the floor holds, then by item 3 it is
not continuous for bounded convergence on any countable set, so the floor is invisible on every countable union of
leaves. Pointwise on countably
many leaves, the defect of `kappa/3 + L` can be driven to `0` inside the ball of radius `1/2 + o(1)`.

## Step 5. The finite-level shadow (item 4)

Let `X` be a finite `Gamma`-set. Put `Omega_X` = the cells of `Y_X`, and `L_X = Z^(Omega_X) + delta C^1(Y_X; R)`.
Let `P = sum_(j<=k) A_j` with `||A_j|| <= b` (for the sup norm) and `P(L_X) subset Z`.

**(a) Bounded support.**
- Step 1 applies verbatim, and Step 2(a) applies with the partition into single cells.
- So the array of `N_k^j j! A_j` in the cell basis has at most `9^j (N_k^j j! b)^2` nonzero entries.
- Hence `P` depends only on `y|F` for a set `F` of at most
  `R(k, b) = sum_(j=1)^k j 9^j (N_k^j j! b)^2` cells.

**(b) Duality on `F`.**
- `L_X|F = Z^F + V`, where `V` is the image of `delta` followed by restriction. `V` is a rational subspace, since
  `delta` has an integer matrix. So `L_X|F` is the preimage of a closed subtorus of `R^F / Z^F`, and it is closed.
- By Pontryagin duality, `L_X|F` is the joint kernel of the characters `e(<n, .>)` with `n in Z^F` and `n perp V`.
- `n perp V` means `<partial n, theta> = 0` for all `theta`, i.e. `n` is an integral 2-cycle of `Y_X` supported on
  `F`.
- So `kappa/3|F in L_X|F` unless some integral 2-cycle `n` supported on at most `R(k, b)` cells has
  `kappa(n) != 0 mod 3`.

**(c) No short detecting cycles at deep levels.**
- Let `n` be such a cycle. Split its support into edge-connected components. Boundaries cancel only between cells
  that share an edge, so each component is itself a cycle.
- A component has at most `R = R(k, b)` cells, each with a boundary loop of length at most `l_max`. So all of its
  vertices lie within `rho = R l_max` of any one of them, say `x`.
- Suppose the covering `Y~ -> Y_X` is injective on the closed ball `B~(x~, rho)` (vertices, edges and cells whose
  boundaries lie in it). Then the component lifts to an integral chain `n~` on `Y~`.
- `partial n~` maps injectively onto `partial n = 0`, so `n~` is a cycle. It carries the same `kappa`, because `kappa_c`
  depends only on the relator of `c`.
- By Step 3 of `deligne-third-floor-no-character-certificate-proof`, `kappa(n~) = 0`. So `kappa(n) = 0`, and
  `kappa/3|F in L_X|F`.
- Take `l in L_X` with `l|F = kappa/3|F`. Then `P(kappa/3) = P(l)`, which lies in `Z`.

**(d) The congruence tower.**
- For `X = Gamma / Gamma(N)`, with `Gamma(N)` normal, injectivity on every `rho`-ball holds as soon as `Gamma(N)`
  meets the word ball of radius `2 rho + 2` only in `1`.
- The intersection of all `Gamma(N)` is `1` (residual finiteness), and word balls are finite. So this holds for all
  `N >= N_0(k, b)`.
- The floor equals the limit of `mu_(1/3)` along the principal congruence tower. Two facts give this: `mu` is
  monotone under pullback, and by the congruence subgroup property of `Sp_4(Z)` (Bass-Milnor-Serre) every
  finite-index subgroup contains some `Gamma(N)`. A proof of the floor by certificates of degree `<= k` and norm `<= b` would need a certificate
  `P(kappa/3) notin Z` at every level. By the above there is none past `N_0(k, b)`. ∎(4)

## What survives

- The kill is uniform in the degree `k` and the norm `b` at each finite level. It is exact (not a limit) in the
  profinite model.
- It does **not** touch:
  - certificates of unbounded degree or norm, such as `dist(., cl L)` itself, or the min-max (K1)/(K2) arguments of
    `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`;
  - spectral or rigidity arguments that act on the uniform structure over uncountably many leaves.
- Also untouched is the refutation side, `kappa/3 in cl L`. By Step 4, this is equivalent to upgrading the bounded,
  countably-pointwise approximants `y_n` to uniform ones.
