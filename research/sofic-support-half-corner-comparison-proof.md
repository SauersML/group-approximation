---
rg: 2
id: sofic-support-half-corner-comparison-proof
kind: route
title: Project the left factor onto the actor subgroup and count with a regular sofic rank
target: sofic-support-cannot-install-half-corner-comparison
requires: []
---

Complete direct proof. Suppose `H = <K, supp Z>` is sofic.

1. **Move `L` into `k[H]`.** Let `E_H : k[G] -> k[H]` keep the coefficients on
   `H`. For `g` outside `H`, `g x` is supported in the coset `gH` for every
   `x in k[H]`, so `E_H(y x) = E_H(y) x` and `E_H(x y) = x E_H(y)`. Since
   `Z, f, P in k[H]`, the element `L' = f E_H(L) P` lies in `f k[H] P` and
   `L' Z = E_H(f L Z) = f`.
2. **A faithful rank function.** Let `sigma_n : H -> Sym(X_n)` be a sofic
   approximation, so that `d(sigma_n(g) sigma_n(g'), sigma_n(g g')) -> 0` and
   `d(sigma_n(g), 1) -> 1` for `g != 1`. Extend `k`-linearly to
   `k[H] -> M_(X_n)(k)`. Modulo matrices of normalized rank tending to zero
   along an ultrafilter, this is a unital ring homomorphism into a ring with
   the Sylvester rank function `rho = lim_omega rank / |X_n|`. By Elek--Szabo
   (Sofic groups and direct finiteness, J. Algebra 280 (2004) 426--434),
   `rho(x) > 0` for every nonzero `x in k[H]`. Directly: if `x != 0` has
   support `F`, the points `y` at which the `sigma_n(g) y`, `g in F`, are
   distinct have density tending to one. A maximal family of such points with
   pairwise disjoint `F`-images has density at least of order `1 / |F|^2`,
   and the corresponding columns of `sigma_n(x)` are nonzero with disjoint
   supports.
3. **`rho` is regular on `K`.** Call `y in X_n` good if the `sigma_n(k) y`,
   `k in K`, are distinct and `sigma_n(k) sigma_n(k') y = sigma_n(k k') y` for
   all `k, k' in K`. Call `y` very good if every `sigma_n(k') y` is good. Bad
   points have density tending to zero, and each `sigma_n(k')` is a
   permutation, so very good points have density tending to one.
   * For very good `y`, the orbit `O_y = sigma_n(K) y` has `|K|` points, is
     `sigma_n(K)`-invariant, and carries the left regular action.
   * Two such orbits are equal or disjoint: if
     `z = sigma_n(k) y = sigma_n(k') y'`, then both orbits equal
     `sigma_n(K) z`.

   So the union `W` of these orbits is a `sigma_n(K)`-invariant set of density
   tending to one, on which `K` acts freely. Its complement is invariant too.
   For an idempotent `p in k[K]`, `sigma_n(p)` preserves `k^W` and
   `k^(X_n \ W)`, and on `k^W` it is a direct sum of `|W| / |K|` copies of
   `p` acting on `k[K]`. Hence
   `rho(p) = dim_k p k[K] / |K|`, the regular rank.
4. **The split embedding is onto.** `D = Z L'` is an idempotent in
   `P k[H] P`, since `D^2 = Z f L' = D`. Sylvester monotonicity gives
   `rho(D) >= rho(L' D Z) = rho(f)` and `rho(f) = rho(L' Z) >= rho(Z L' Z L') = rho(D)`,
   so `rho(D) = rho(f)`. `P - D` is an idempotent orthogonal to `D`, so
   `rho(P - D) = rho(P) - rho(f) = 0` by step 3 and the equal regular ranks.
   Faithfulness gives `D = P`.
5. **Contradiction.** `Z L' = P` and `L' Z = f`, with `Z in P k[G] f` and
   `L' in f k[G] P`. So `f` and `P` are Murray--von Neumann equivalent in
   `k[G]`, against the hypothesis. `square`

**The half-corner hypothesis.** `ev(f) = 0` gives
`ev(Z) = ev(P) ev(Z) ev(f) = 0`. So an equivalence `Z L' = P` would force
`ev(P) = 0`, contradicting `ev(P) = p_01 != 0`, for both `(f_+, P)` and
`(f_0, P_0)`.
