---
rg: 2
id: toms-ancestor-twisted-cubes-proof
kind: route
title: Run the cube proof over Y x Z, read off the u-multidegree (1,...,1) part of the twisted alternant as a Vandermonde in the path twists, and show it is non-zero by its leading monomial at the last common ancestors
target: toms-ancestor-twisted-cubes-force-depth-k-over-2
requires: []
---

Notation is from the target. Cohomology has rational coefficients. `toms-sibling-cube-depth-n-proof`
is cited as [C], with its Steps 1–6.

**Step 1 (the cube proof over `Y x Z`).** Replace `Y` by `Y' = Y x Z` throughout [C].
- [C] Step 1 is about the band space `X` alone.
- [C] Steps 2, 4 and 5 use only that `P_G` and the `P_a` are mutually orthogonal projections
  over the parameter space, and that the weights depend on `s` alone. So they hold over `Y'`.
- In [C] Step 3 the chamber `(sigma, pi)` has `W = G ⊕ L_(pi(1))` and `ell_i = L_(pi(i+1))`, with
  `L_nu = L_(nu, sigma_nu)`. So with `x_(nu,±) = c_1(L_(nu,±))` the class `omega` pulls back to
  `(ch_(m_1)(G) + x_(pi(1))^(m_1)/m_1!) prod_(k >= 2) x_(pi(k))^(m_k)`.

  Sum over `sigma` one node at a time, with weight `prod sigma`. The `ch(G)` term does not
  depend on `sigma_(pi(1))`, so it cancels. The factor of node `pi(k)` becomes
  `x_(pi(k),+)^(m_k) - x_(pi(k),-)^(m_k)`. Summing over `pi` with `sign(pi)` gives

  ```text
  e^* Omega = ± (1/m_1!) det[ x_(nu,+)^(m_k) - x_(nu,-)^(m_k) ]_(k, nu)   in H^(N-1)(S^(N-1)) ⊗ H^*(Y').
  ```

  This uses no relation between `x_(nu,+)` and `x_(nu,-)`. The script checks the identity
  symbolically for `N = 2, 3`.
- [C] Step 6 uses only that `1 ⊗ H^*(Y')` meets `F^1` in `0`, which holds for any `Y'`.

So Theorem 1 follows once `e^* Omega != 0`.

**Step 2 (the multidegree-(1,...,1) part).** Take `m_k = k`. Write
`f_k(nu) = (alpha u_nu + A_nu)^k - (beta u_nu + A_nu)^k = sum_(i = 1..k) C(k,i) (alpha^i - beta^i) u_nu^i A_nu^(k-i)`.
The `i = 0` terms cancel, so every entry of column `nu` is divisible by `u_nu`.

`H^*(Y') = H^*(Y) ⊗ H^*(Z)`, and `H^*(Y)` is graded by the multidegree in `(u_1, ..., u_N)`.
In the permutation expansion of the determinant, each term takes one entry from each column.
Its part of multidegree `(1, ..., 1)` is the product of the `i = 1` terms,
`k (alpha - beta) u_nu A_nu^(k-1)`. Hence that part of `det[f_k(nu)]` is

```text
prod_k k (alpha - beta) · u_1 ... u_N · det[A_nu^(k-1)]_(k, nu) = ± N! (alpha - beta)^N u_1 ... u_N V(A).
```

`u_1 ... u_N != 0` in `H^*(Y)`, because every `j_nu >= 1`. A tensor product of non-zero classes
over `Q` is non-zero. So `V(A) != 0` gives `e^* Omega != 0`, and Theorem 1 follows by Step 1.
The factor `1/m_1! = 1` does not matter.

**Step 3 (Theorem 2).** Order the variables `u_rho` by height in the tree, higher vertices
larger, with ties broken arbitrarily. Use the lexicographic monomial order on
`Q[u_rho]`.

Take `nu != nu'` with last common ancestor `rho`. The two paths agree above `rho`, so those
terms cancel in `A_(nu') - A_nu`. At `rho` the paths leave through different children, so the
coefficient of `u_rho` is `±(alpha - beta) != 0`. Every other variable that remains lies strictly
below `rho` on one of the two paths. So the leading term of `A_(nu') - A_nu` is `±(alpha - beta) u_rho`.

The leading monomial of a product is the product of the leading monomials, and the
coefficient multiplies. So `V(A)` has leading monomial `prod_rho u_rho^(c_rho)`, where `c_rho` is
the number of pairs with last common ancestor `rho`, that is `a_rho b_rho`. Its coefficient is
`±(alpha - beta)^(N(N-1)/2)`.

`H^*(Z) = Q[u_rho] / (u_rho^(j_rho + 1))` is a quotient by a monomial ideal. A polynomial has
non-zero image iff it has a monomial outside the ideal with non-zero coefficient. The
leading monomial is outside the ideal when `c_rho <= j_rho` for all `rho`, and its coefficient is
non-zero. So `V(A) != 0`.

**Step 4 (Toms's tower).** From `toms-twisted-swap-pairs-are-totally-degeneracy-forcing`:
`phi_i(f) = f∘pi_1 ⊗ gamma_(i,1) ⊕ f∘pi_2 ⊗ gamma_(i,2)`, with `gamma_(i,1)`, `gamma_(i,2)` pulled back from
`O(1)`, `O(2)` (up to the sign convention) on the factor `CP^(j_i)` of
`X_(i+1) = X_i x X_i x CP^(j_i)`. Iterating, `phi_(n+1,M)` sends `E` to the sum over the copies of
the level-`n` nodes, and the copy of `nu` is `E` pulled back and tensored with
`Gamma_nu = ⊗_(rho above nu) gamma_(rho, child)`.

In the window box of the depth-one transports
(`toms-sibling-cube-swap-drops-add-to-depth-n`, window-box corollary), the facet lines of
`nu` are `ell ⊗ gamma_(nu,1) ⊗ Gamma_nu` and `ell' ⊗ gamma_(nu,2) ⊗ Gamma_nu`. Here `ell` and `ell'` are pulled back
from the swap path in the leaves, which is contractible, so they are trivial on `F`. So
`c_1 = alpha u_nu + A_nu` and `beta u_nu + A_nu`, with `A_nu = c_1(Gamma_nu)` of the tree form of Theorem 2,
and `alpha != beta` for Toms's twists.

Take all `K/2` level-`n` nodes. An ancestor at level `n + l` has `2^(l-1)` of them below each
child, so `a_rho b_rho = 4^(l-1)`. Since `d_(n+l) = 2^l d_n`, we have `j_rho = 2 · 4^l d_n^2 >= 4^(l-1)`.
Theorems 1 and 2 give a point of `F` with `rank Q <= g`, a drop of depth `K/2` below the upper
band `g + K/2`. In `A` one stage-`M` rank is `1/d_M = 1/(K d_n)` on point traces, so the drop is
`1/(2 d_n)`.

For `B`, the telescoped top map is the Section 4 diagonal map
(`toms-simple-algebra-no-block-diagonal-realizer-proof`, imports). So the top blocks of
`psi_(n,M)` carry the same path twists. Point blocks are constant fields: in a window box
they lie in `G`, and `ch(G)` cancels in Step 1. The trace of one stage-`M` rank on a branch
trace is `beta_M / r_M`, and `K beta_M/(2 r_M) = beta_n/(2 r_n)`.

**Step 5 (weights and the Hall count).**
- *Weights.* `phi_(r+1,M)` has one block for each copy of a level-`r` node, of the same rank
  as its argument. So a window drop of one rank at such a node is one stage-`M` rank.
- *Hall count.* Nodes of level `n + l` have `j = 2 d_n^2 4^l`. A choice of `a_l <= K/2^(l+1)`
  nodes per level satisfying Hall has `sum_(l' <= l) a_(l') <= 2 d_n^2 4^l`. Choose `l*` with
  `8^(l*)` close to `K/d_n^2`. Then `N <= sum_(l <= l*) 2 d_n^2 4^l + sum_(l > l*) K/2^(l+1) = O((d_n K)^(2/3))`.

**Step 6 (calibration and computation).**
- If `alpha = beta`, every entry `f_k(nu)` is `0`.
- If `A = 0`, Step 1 gives back [C]'s alternant.
- In the product model, the transport of node `nu` is a section of `Hom(L_(nu,-), L_(nu,+))`, which
  is `gamma_(nu,1) ⊗ gamma_(nu,2)^*` with `Gamma_nu` cancelled. So it extends over `Z`, and its common
  drop is the one Theorem 1 forces.

`ancestor_cube.py` checks the following:
- the Step 1 identity, for `N = 2, 3` and four exponent systems;
- the full determinant for `N = 2, 4`, `j in {1, 2, 3}`, four twist pairs and minimal room;
- `V(A)` for `N = 2, 4, 8`.

All are non-zero, and the two calibrations give `0` (`results.json`). Square.
