---
rg: 2
id: deligne-lattice-hyperlinear-iff-full-hs-parameter-circle-proof
kind: route
title: Cut the central unitary by a spectral projection of a short arc in the tracial ultraproduct, and read the corner as an HS model at the arc's centre
target: deligne-lattice-hyperlinear-iff-full-hs-parameter-circle
requires:
  - deligne-hs-parameter-trace-threshold
  - finitely-generated-linear-groups-are-residually-finite
---

Notation as in the claim.
- Write elements of `Gamma~` uniquely as `z^a s(g)`, where `s(g) s(h) = z^(b(g,h)) s(gh)`, `b` is normalized and
  `s(e) = e` (as in `deligne-lattice-non-mf-forces-finite-parameter-group-proof`).
- In `M = prod_omega M_(k_n)`, `||[x_n]||_2 = lim_omega ||x_n||_2`, and `tau` is faithful on `M`.
- `B_W = max_W |b|` for a finite window `W` of pairs.

Four standard ultraproduct facts are used.
- **(F1) Corners.** Let `p` be a projection in `M` with `tau(p) > 0`. Lift `p` to projections `p_n` of rank `r_n`.
  Then `pMp`, with trace `tau(p .)/tau(p)`, is `prod_omega p_n M_(k_n) p_n = prod_omega M_(r_n)`, again a tracial
  ultraproduct of matrix algebras.
- **(F2) Unitary lifts.** Every unitary of `prod_omega M_(r_n)` is the class of a sequence of unitaries (polar
  decomposition of any lift), and the unit lifts to `I`.
- **(F3) Diagonal extraction.** Suppose that for every finite window `W` and every `eps > 0` there are `d` and a map
  `U : Gamma -> U(d)` with `U(e) = I` and `||U(g)U(h) - c_s(g,h) U(gh)||_2 < eps` on `W`. Then `s` is in `P_2`: take
  windows `W_j` increasing to `Gamma x Gamma` and `eps_j = 1/j`.
- **(F4) Weighted block sums.** For maps `U_i : Gamma~ -> U(d_i)`, `i = 0..n`, and rational weights `w_i > 0` with sum
  `1`, choose `D` with `a_i = w_i D / d_i` integral and put `U = direct_sum_i U_i^((+) a_i)`. Then for every
  `X_i in M_(d_i)`, `||direct_sum_i X_i^((+) a_i)||_2^2 = sum_i w_i ||X_i||_2^2`.

## Step 1: tracial spectral support (H1)

Let `lambda = e(s_0)` be in `supp(mu)`. Fix `0 < r < 1/4` and the closed arc `I_r = { e(t) : |t - s_0| <= r }`.
1. `p = 1_(I_r)(u)` is in `W*(u)` and `tau(p) = mu(I_r) > 0`, because `lambda` is in the support.
2. `u = V(z)` commutes with `V(Gamma~)`, so all of `W*(u)` does. Hence `p` commutes with `V(Gamma~)`, and
   `pi(gamma) = p V(gamma)` is a unitary representation of `Gamma~` in `pMp`.
3. By the spectral theorem, `||pi(z) - lambda p|| <= sup_(zeta in I_r) |zeta - lambda| <= 2 pi r` in operator norm.
4. Put `W(g) = pi(s(g))`. Then
   ```text
   W(g)W(h) - c_(s_0)(g,h) W(gh)  =  (pi(z)^(b(g,h)) - lambda^(b(g,h))) W(gh),
   ```
   because `c_(s_0)(g,h) = lambda^(b(g,h))`. By `|x^k - y^k| <= |k||x - y|` for commuting unitaries, its operator
   norm is at most `2 pi r |b(g,h)|`, and `||.||_2 <= ||.||`.
5. By (F1) and (F2), `pMp = prod_omega M_(r_n)`, and the `W(g)` lift to unitaries `W_n(g)` with `W_n(e) = I`
   (`W(e) = p` is the unit of `pMp`). For a finite window `W_0`,
   ```text
   lim_omega max_(W_0) ||W_n(g)W_n(h) - c_(s_0)(g,h) W_n(gh)||_2  <=  2 pi r B_(W_0) .
   ```
   So for each `eps` pick `r < eps / (2 pi B_(W_0) + 1)` and then `n` in an `omega`-large set.
6. By (F3), `s_0` is in `P_2`. `QED (H1)`.

The same argument applies to any homomorphism `Gamma~ -> E_q -> U(M)`, with `u` of order dividing `q`.

## Step 2: gluing a parameter to the residually finite base

**Lemma G.** Let `s` be in `P_2`, and let `q` be the order of `s` in `R/Z` (`q = infinity` if `s` is irrational). Then
`Gamma~/<z^q>` is hyperlinear (for `q = infinity`, `Gamma~` itself).

*Proof.*
1. Take `U_n : Gamma -> U(d_n)` at `s` as in the definition of `P_2`, with `U_n(e) = I`.
2. `Gamma` is finitely generated and linear, hence residually finite
   (`finitely-generated-linear-groups-are-residually-finite`). Enumerate finite quotients `Gamma -> F_k`, `k >= 1`, so
   that every `g != e` survives in some `F_k`. Let `lambda_k` be the regular representation of `F_k`, pulled back to
   `Gamma~` along `z^a s(g) -> g`.
3. Put weights `w_0 = 1/2 + 2^(-n-1)` and `w_k = 2^(-k-1)` for `1 <= k <= n`; they sum to `1`. By (F4), let
   `A_n(z^a s(g))` be the weighted block sum of `e(as) U_n(g)` and of `lambda_1(g), ..., lambda_n(g)`, in dimension
   `D_n`. Put `A = [A_n] : Gamma~ -> U(prod_omega M_(D_n))`.
4. *Homomorphism.* In `A_n(gamma)A_n(gamma') - A_n(gamma gamma')`, the `lambda_k` blocks vanish exactly. The first
   block is `e((a+c)s)(U_n(g)U_n(h) - c_s(g,h)U_n(gh))`, since `e((a+c+b(g,h))s) = e((a+c)s) c_s(g,h)`. Its
   `||.||_2` tends to `0`, and by (F4) its weight is at most `1`. So `A` is a homomorphism. It factors through
   `Gamma~/<z^q>`, because `A(z^q) = e(qs) = 1`.
5. *Injective on the quotient.* Take `gamma = z^a s(g)`.
   - If `g != e`, pick `k` with `g` nontrivial in `F_k`. Then `lambda_k(g)` is a fixed-point-free permutation matrix,
     so `||lambda_k(g) - 1||_2^2 = 2`. For `n >= k`, `||A_n(gamma) - 1||_2^2 >= 2 w_k = 2^(-k)`.
   - If `g = e` and `a` is not divisible by `q`, then `||A_n(z^a) - 1||_2^2 >= w_0 |e(as) - 1|^2 >= |e(as) - 1|^2/2 > 0`.

   In both cases `A(gamma) != 1`. `QED`

This is the HS copy of Step 1 of `deligne-lattice-non-mf-forces-finite-parameter-group-proof`.

## Step 3: (H2) and (H3)

**(H2), "if".** `P_2 = R/Z` contains an irrational `s`, and Lemma G gives `Gamma~` hyperlinear.

**(H2), "only if".** Let `V : Gamma~ -> U(M)` be injective, and suppose `P_2 = (1/m_2)Z/Z`.
1. By (H1), `supp(mu)` lies in `mu_(m_2)`.
2. So `tau(|u^(m_2) - 1|^2) = integral |zeta^(m_2) - 1|^2 d mu = 0`.
3. Since `tau` is faithful, `V(z^(m_2)) = 1`, which contradicts injectivity.

So `P_2` is infinite, and `P_2 = R/Z` by (T1).

**(H3).**
- *Kernel.* The same computation shows that every homomorphism `V : Gamma~ -> U(M)` kills `z^(m_2)`.
- *Quotient.* `1/m_2` is in `P_2` and has order `m_2`. Lemma G makes `E_(m_2)` hyperlinear.
- *Radical.* Hence the intersection of all kernels is exactly `<z^(m_2)>`.

**`E_q` hyperlinear iff `1/q` is in `P_2`.**
- *If.* Apply Lemma G at `s = 1/q`.
- *Only if.* Let `V : E_q -> U(M)` be injective, with `u = V(z)` and `u^q = 1`.
  1. By (H1), applied to `Gamma~ -> E_q -> U(M)`, `supp(mu)` lies in `mu_q cap e(P_2)`.
  2. `P_2 cap (1/q)Z/Z` is a subgroup `(1/q')Z/Z` with `q'` dividing `q`.
  3. If `1/q` is not in `P_2`, then `q' < q`. Faithfulness of `tau` gives `u^(q') = 1`, and `z^(q') != e` in `E_q`,
     which contradicts injectivity. So `1/q` is in `P_2`.

At `q = 3` this is (T5).

## Step 4: tracial visibility in coronas (H4)

1. `x = [(x_n)] -> [(x_n)]_omega` is a well-defined unital *-homomorphism `pi_omega : Q -> M_omega = prod_omega M_(d_n)`,
   because `||x_n|| -> 0` implies `||x_n||_2 -> 0`.
2. `V = pi_omega o Theta` is a homomorphism `Gamma~ -> U(M_omega)`, and `V(z) = [u_n]_omega`. Its `tau_omega`-moments
   are `lim_omega tr(u_n^k)`, so its distribution is the `omega`-limit of the eigenvalue distributions of `u_n`.
3. That distribution is supported in `sp(V(z))`, which lies in `sp(Theta(z))` since `pi_omega` is unital. By (H1)
   it is also supported in `e(P_2)`.
4. If `P_2 = (1/m_2)Z/Z`, Step 3 gives `lim_omega ||u_n^(m_2) - 1||_2 = 0` for every free `omega`. A bounded real
   sequence whose limit along every free ultrafilter is `0` tends to `0`. `QED (H4)`

## Step 5: the split (H5) and the class kill

**(H5).** Assume (HL) and (IR), and let `Theta` be an injective corona homomorphism of `Gamma~`. By (H4) and (HL),
`||u_n^(m_2) - 1||_2 -> 0`. By (IR), `Theta(z^(m_2)) = 1`, which contradicts injectivity. So `Gamma~` is not MF.

**Class kill.** Let `Theta` be tracially visible as in the claim. Suppose `P_2` were finite. Then (H4) at `N = m_2`
gives `||Theta(z)^(m_2) - 1||_(2,omega) = 0` for every `omega`, which contradicts visibility. So `P_2 = R/Z`, and
`Gamma~` is hyperlinear by (H2).

**Where (IR) sits.**
- *Upper bound.* On (HL), (IR) follows from the instance `(CPE*)` of `commutant-projection-extraction` at
  `(Gamma~, z^(m_2))`. Suppose `||Theta(z^(m_2)) - 1|| >= delta`. `(CPE*)` gives a nonzero projection `q` in the
  commutant and `|nu - 1| >= delta` with `||(Theta(z^(m_2)) - nu) q|| <= eta < delta/2`.
  1. Lift `q` to projections `q_n`. After passing to the infinitely many `n` with `q_n != 0`, `q Q q` is the norm
     matrix corona of the blocks `q_n M_(d_n) q_n`.
  2. `q Theta q` is a corona model of `Gamma~` there, and every limit trace of it gives
     `||Theta(z)^(m_2) - 1||_2 >= delta - eta > 0`.
  3. This contradicts (H4) for that model. Note that (H4) is applied to the corner's own normalized traces, so it
     costs nothing when `rank(q_n)/d_n -> 0`.
- *Not empty in general.* `commutant-projection-extraction` is REFUTED by
  `o2-suspension-central-unitary-evades-commutant-corners`. So a proof of (IR) must use `Gamma~` itself, for example
  property (T) or the Maslov cocycle, and not general corona theory.
- *Where the tracial proof dies in norm.* Step 1 needs the projection `1_(I_r)(u)`. In `Q` the spectrum of
  `Theta(z)` off `mu_m` consists of nondegenerate arcs (item 4 of `deligne-lattice-non-mf-forces-finite-parameter-group`).
  `C*(Theta(z))` has no projection cutting such an arc, and no commutant projection need exist. This is the one step
  that fails, and (IR) is exactly what is needed to replace it.
