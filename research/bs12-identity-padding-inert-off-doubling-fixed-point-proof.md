---
rg: 2
id: bs12-identity-padding-inert-off-doubling-fixed-point-proof
kind: route
title: The spectral projection of Z at 1 is squaring-invariant hence reducing; otherwise cut off the fixed space and bound almost-invariant vectors by cycle length
target: bs12-identity-padding-inert-off-doubling-fixed-point
requires: []
---

Notation is as in the target. All operators are on finite-dimensional spaces, all norms are operator norms, and `E_Z(X)` is the spectral projection of a normal `Z` onto `X`. `P` is the orthogonal projection onto `V`. Both `M` and `N` commute with `P`, and `N x = x` for `x in V`.

## Four standard facts, proved here

**(F1) Spectra move by at most the perturbation.** If `N` is normal and `||Z-N|| <= eps`, then every `lambda in spec(Z)` has `dist(lambda, spec N) <= eps`.
- If `dist(lambda, spec N) > eps`, then `||(N-lambda)^(-1)|| = 1/dist < 1/eps`, because `N` is normal.
- So `Z - lambda = (N-lambda)(1 + (N-lambda)^(-1)(Z-N))` is invertible.

**(F2) Squaring permutes the spectrum.** If `C Z C^* = Z^2` exactly, then `C E_Z(X) C^* = E_(Z^2)(X) = E_Z(sigma^(-1) X)`, where `sigma(lambda) = lambda^2`.
- `spec(Z) = spec(Z^2) = sigma(spec Z)`. The set is finite, so `sigma` is a bijection of `spec Z`.
- Every element of `spec Z` is a root of unity of odd order.
- `C` maps `ker(Z - lambda)` onto `ker(Z - sigma^(-1)(lambda))`, the eigenspace of the unique square root of `lambda` in `spec Z`. Indeed, if `Zv = lambda v` then `Z^2 (Cv) = C Z v = lambda Cv`. In particular `F = ker(Z-1)` satisfies `C F = F`, so `F` and `F^perp` reduce `(C,Z)`.

**(F3) Any orbit other than 1 leaves the disc of radius √2.** If `lambda != 1` is in a finite `sigma`-invariant set of roots of unity, some `sigma^j(lambda)` has `|sigma^j(lambda) - 1| >= sqrt(2)`.
- Write `lambda = e^(2 pi i theta)` with `theta in (-1/2, 1/2]` and `theta != 0`.
- While `|theta| < 1/4`, doubling doubles `|theta|`. So some iterate has representative angle `theta_j` with `1/4 <= |theta_j| <= 1/2`.
- Then `|lambda_j - 1| = 2 |sin(pi theta_j)| >= 2 sin(pi/4) = sqrt(2)`.

**(F4) A rotation carries one projection to a close one.** Let `P, P'` be projections with `s := ||(1-P')P|| + ||P'(1-P)|| < 1`. Put `T = P'P + (1-P')(1-P)`.
- Then `T - 1 = -(1-P')P - P'(1-P)`, so `||T-1|| <= s`, and `T` is invertible.
- `T P = P' P = P' T`, and `T^*T = P P' P + (1-P)(1-P')(1-P)` commutes with `P`.
- So `W = T |T|^(-1)` is unitary with `W P = P' W`, that is, `W P W^* = P'`.
- The singular values of `T` lie in `[1-s, 1+s]`, so `|| |T| - 1 || <= s`. Hence `||W - 1|| <= ||T-1|| + || |T| - 1 || <= 2s`.

**(F5) Equal-rank projections are close in both directions.** If `rank P = rank P'` and `||(1-P')P|| = t < 1`, then `||P'(1-P)|| <= t`.
- For `x` in the range of `P`, `||P'x||^2 = ||x||^2 - ||(1-P')x||^2 >= (1-t^2) ||x||^2`.
- So the square map `P'P` from `ran P` to `ran P'` has smallest singular value at least `sqrt(1-t^2)`.
- Its adjoint is `P P'` from `ran P'` to `ran P`. It has the same singular values, so `||P y||^2 >= (1-t^2)||y||^2` for `y` in the range of `P'`.
- Hence `||(1-P)y|| <= t ||y||`.

**(T) Transport lemma.** Let `(C',Z')` be an exact packet on `C^n (+) C^k` that commutes with a projection `P'`. Suppose `s = ||(1-P')P|| + ||P'(1-P)|| < 1`, and let `W` be as in (F4).
- `(W^*C'W, W^*Z'W)` is an exact packet that commutes with `P`.
- Its compressions `(C_0, Z_0)` to `C^n (+) 0` are unitary and satisfy `C_0 Z_0 C_0^* = Z_0^2`, since block-diagonal unitaries multiply blockwise.
- `||C_0 - A|| <= ||W^*C'W - M|| <= ||C' - M|| + 4s`, and likewise `||Z_0 - B|| <= ||Z' - N|| + 4s`.

## Item 1: gapped removal

Assume `k >= 1` and `n >= 1`; the other cases are trivial. Then `gamma <= 2`, and `eps < gamma/8 <= 1/4`.

- **The projection.** By (F1), `spec Z` lies within `eps` of `{1} ∪ spec B`. Points within `eps` of `spec B` are at distance at least `gamma - eps > eps` from `1`. Let
  `P' = E_Z(D[1,eps])`, the projection for the closed disc.
- **Padding vectors lie near ran P'.** Take a unit `x` in `V`. Since `Nx = x`, `||(Z-1)x|| <= eps`. `Z` commutes with `P'`, and on `ran(1-P')` its spectrum is at distance at least `gamma - eps` from `1`. So
  `eps >= ||(Z-1)x|| >= ||(Z-1)(1-P')x|| >= (gamma-eps) ||(1-P')x||`,
  and `||(1-P')P|| <= eps/(gamma-eps) <= 2 eps/gamma`.
- **Vectors of ran P' lie near V.** Take a unit `y` in `ran P'`. Then `||(Z-1)y|| <= eps`, so `||(N-1)y|| <= 2 eps`. But `N - 1 = (B-1) (+) 0` and `||(B-1)u|| >= gamma ||u||`, since `B` is normal with `dist(1, spec B) >= gamma`. So `||(1-P)y|| <= 2 eps/gamma`, and `||P'(1-P)|| <= 2 eps/gamma`.
- **Rank.** Hence `||P' - P|| <= 2eps/gamma < 1/4`, and `rank P' = rank P = k`.
- **Squaring invariance.** `M` commutes with `P`, so
  `||C P' C^* - P'|| <= ||C P' C^* - M P' M^*|| + ||M (P'-P) M^* - (P'-P)|| <= 2 eps + 4 eps/gamma < 1/2 + 1/2 = 1`.
  By (F2), `C P' C^* = E_Z(sigma^(-1) D[1,eps])`. Both it and `P'` are spectral projections of the same normal `Z`. The difference of two spectral projections of one normal operator is a sum of eigenprojections with coefficients in `{-1,0,1}`, so its norm is `0` or `1`. Hence `C P' C^* = P'`.
- **The spectral set is exactly {1}.** Put `S = spec Z ∩ D[1,eps]`. The equality says: for `lambda in spec Z`, `lambda in S` if and only if `sigma(lambda) in S`. Since `sigma` permutes `spec Z` (F2), `S` is `sigma`-invariant. `S ⊂ D[1,eps]` and `eps < sqrt(2)`, so by (F3) `S ⊂ {1}`. `S` is nonempty because `rank P' = k >= 1`. So `S = {1}` and `P' = ker(Z-1)`.
- **Transport.** `C` and `Z` commute with `P'`. Apply (T) with `s <= 4 eps/gamma`. This gives an exact packet `(C_0, Z_0)` in `U(n)` with
  `||C_0 - A||, ||Z_0 - B|| <= eps + 16 eps/gamma`.
- **Arbitrary padding with b trivial.** The argument used only three facts: `N` is `B (+) 1_k`, `M` commutes with `P`, and (P) holds. So it applies verbatim with `M = A (+) U` for any `U in U(k)`. ∎

## Item 2: localization

Here `M = A (+) 1_k`, so `M x = x` and `N x = x` for `x in V`. Let `P_F` be the projection onto `F = ker(Z-1)`. By (F2), `P_F` commutes with `C` and `Z`. Put `U = C|F` and `r = sqrt(eps)`. Let `Q <= P_F` be the spectral projection of `U` for the closed disc `D[1,r]`.

- **Q is reducing and trivial up to r.** `Q` commutes with `C`, and `Z = 1` on `ran Q`. Define `C~ = C(1-Q) + Q`. Then `(C~, Z)` is an exact packet: on `ran(1-Q)` it is `(C,Z)`, and on `ran Q` it is `(1,1)`. Also `||C~ - C|| = ||(U-1)Q|| <= r`.
- **Padding vectors lie near ran Q.** Take a unit `x` in `V`, and write `f = P_F x`, `g = x - f`, with `g` in `G`. Since `C` and `Z` commute with `P_F`,
  `||Cg-g||^2 + ||Zg-g||^2 <= ||Cx-x||^2 + ||Zx-x||^2 = ||(C-M)x||^2 + ||(Z-N)x||^2 <= 2 eps^2`.
  So `kappa ||g|| <= sqrt(2) eps`.
  Also `||(U-1)f|| = ||P_F (C-1) x|| <= eps`. On `ran(P_F - Q)` the spectrum of `U` is at distance more than `r` from `1`, so `||(P_F-Q) f|| <= eps/r = sqrt(eps)`. Hence
  `||(1-Q)x|| <= ||g|| + ||(P_F-Q)f|| <= sqrt(2) eps/kappa + sqrt(eps) = d`.
- **A trivial subspace close to V.** Since `d < 1`, `Q` is injective on `V`. Let `P'` be the projection onto `V' = Q V`, which has dimension `k`. For a unit `x` in `V`, `dist(x, V') <= ||x - Qx|| <= d`, so `||(1-P')P|| <= d`. By (F5), `||P'(1-P)|| <= d`. `V'` lies in `ran Q`, where `(C~,Z)` acts as the identity, so `P'` commutes with `C~` and `Z`.
- **Transport.** Apply (T) to `(C~, Z)` and `P'`, with `s <= 2d < 1`. Since `||C~ - M|| <= eps + sqrt(eps)` and `||Z - N|| <= eps`,
  `||C_0 - A|| <= eps + sqrt(eps) + 8d`,     `||Z_0 - B|| <= eps + 8d`.
- **The numerical form.** If `kappa >= sqrt(eps)` and `eps <= 1/64`, then `d <= (1+sqrt 2) sqrt(eps) < 1/2`, and `8d <= 19.4 sqrt(eps)`. Also `eps <= sqrt(eps)/8`. So both errors are at most `22 sqrt(eps)`. ∎

## Item 3: long constituents

- **Minimum over constituents.** `(C,Z)|G` is a finite-dimensional unitary representation, so `G` is an orthogonal sum of irreducible reducing subspaces `G_j`. For `x = sum x_j`,
  `||Cx-x||^2 + ||Zx-x||^2 = sum_j (||Cx_j-x_j||^2 + ||Zx_j-x_j||^2)`.
  So the infimum defining `kappa` is the minimum of the corresponding constants `kappa_j` of the `G_j`.
- **Irreducible packets are cycles.** Let `(C,Z)` be irreducible on a space of dimension `L`, with no nonzero `Z`-fixed vector.
  - By (F2), the eigenspaces over one `sigma`-orbit `O` of `spec Z` span a reducing subspace, so `spec Z = O`.
  - Let `l = |O|` and `lambda in O`. `C^l` preserves `ker(Z-lambda)`; pick a unit eigenvector `u` there, with `C^l u = mu u`.
  - `span{u, Cu, ..., C^(l-1)u}` is invariant under `C` and `Z`, hence reducing, hence everything. So `L = l`.
  - `e_j = C^j u` is an orthonormal eigenbasis, since the vectors lie in distinct eigenspaces. It has `Z e_j = lambda_j e_j` with `lambda_j = sigma^(-j)(lambda) != 1`, `C e_j = e_(j+1)` for `j < L-1`, and `C e_(L-1) = mu e_0`.
  - `L >= 2`, because `lambda^2 = lambda` forces `lambda = 1`.
- **The bound 1/L.** Let `v = sum v_j e_j` be a unit vector, and put `q^2 = ||Cv-v||^2 + ||Zv-v||^2`.
  - By (F3) there is `j0` with `|lambda_(j0) - 1| >= sqrt(2)`. So `2 |v_(j0)|^2 <= ||Zv-v||^2 <= q^2`.
  - `||Cv-v||^2 = sum_(j>=1) |v_j - v_(j-1)|^2 + |v_0 - mu v_(L-1)|^2`. So the cyclic sequence `a_j = |v_j|` has `sum_j (a_j - a_(j-1))^2 <= q^2`.
  - Let `j` be at cyclic distance `m_j <= L/2` from `j0`. By Cauchy--Schwarz, `a_j <= a_(j0) + sqrt(m_j) q`. So `a_j^2 <= 2 a_(j0)^2 + 2 m_j q^2 <= q^2 + 2 m_j q^2`.
  - Summing, and using `sum_j m_j <= L^2/4`: `1 <= L q^2 + (L^2/2) q^2 <= L^2 q^2`, since `L >= 2`.
  - Hence `q >= 1/L`, and every irreducible constituent `G_j` has `kappa_j >= 1/dim G_j`.
- **Conclusion.** If the conclusion of Item 2 at cost `22 sqrt(eps)` is not available, then `kappa < sqrt(eps)`, since `eps <= 1/64` is the other hypothesis. So some constituent has `kappa_j < sqrt(eps)`, hence `dim G_j > 1/sqrt(eps)`, and it carries a unit vector with `q < sqrt(eps)`. ∎
