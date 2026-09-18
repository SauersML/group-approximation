---
rg: 2
id: toms-sibling-cube-depth-n-proof
kind: route
title: Homotope the boundary of the target to the cross-polytope model inside the width-N rank band, and detect it by a top-column Mayer-Vietoris class whose chamber sum is an alternant
target: toms-sibling-cube-swap-drops-add-to-depth-n
requires: []
---

Notation is from the target. Cohomology is singular, with rational coefficients. The
proof follows `toms-two-sibling-depth-two-proof` step by step. Only Steps 2 and 3 are new.

**Step 1 (the band space and its cover).** Let `X = X_(g,N)(n)` be the space of positive
`Q in M_n` with `g + 1 <= rank Q <= g + N`, with eigenvalues `lambda_1 >= lambda_2 >= ...`. For
`k = 1, ..., N` put `U_k = {lambda_(g+k) > lambda_(g+k+1)}`. A matrix of rank `g + r` lies in
`U_r`, so the `U_k` cover `X`. For `T ⊆ {1, ..., N}` put `U_T = ∩_(k in T) U_k`. On `U_T` the
spectral projections onto the top `g + t` eigenvalues, `t in T`, are continuous
(holomorphic calculus), so the subspaces `W_(g+t)` form a continuous flag. On
`U_full = U_(1..N)` put `W = W_(g+1)` and `ell_i = W_(g+i+1)/W_(g+i)`, `y_i = c_1(ell_i)`. Fix
distinct `m_1, ..., m_N >= 1` and put

```text
omega = ch_(m_1)(W) · y_1^(m_2) · ... · y_(N-1)^(m_N)   in  H^q(U_full),   q = 2 sum m_k.
```

The Mayer–Vietoris spectral sequence of the cover has `E_1^(p,q) = ⊕_(|T| = p+1) H^q(U_T)`
and converges to `H^*(X)`. The column `p = N - 1` is the last one, so `omega` is a
permanent cycle. Its class lies in `E_infinity^(N-1,q) = F^(N-1) H^(N-1+q)(X)`. Let `Omega` be
that class.

**Step 2 (the pulled-back cover of the sphere).** By the homotopy argument of Step 4,
any two weight systems as in the target give maps `∂S x Y -> X` that are homotopic inside
`X` (straight-line homotopy of the weights, at most one side per node positive, rank
between `g + 1` and `g + N`). So take
`x = 2s - 1 in ∂[-1,1]^N`, `v_nu = sgn(x_nu) max(0, |x_nu| - c)` for some `c` close to `1`,
`w_(nu,+) = max(0, v_nu)/(1-c)`, `w_(nu,-) = max(0, -v_nu)/(1-c)`, and `e = 2 P_G + sum w_a P_a`.
The weights are at most `1 < 2`. So at every point `W_(g+t) = G ⊕` (the lines of the `t`
largest weights). Also `v` never vanishes, and `v` is homotopic to `x` through non-zero
vectors, since `v_nu x_nu >= 0` with equality not everywhere. So `v/|v| : ∂S -> S^(N-1)` has
degree `1`, and `e` depends on `s` only through `v/|v|`.

Pull the cover back to `S^(N-1)`. A point `v` lies in `U_t` exactly when the `t`-th and
`(t+1)`-th largest of the `|v_nu|` differ, with the `(N+1)`-th taken to be `0`. So the
components of `U_T` are indexed by chains of faces `tau_t`, `t in T`, of the cross-polytope,
with `|tau_t| = t` and each `tau_t` the set of the `t` largest weights. Each component is
contractible. Shrink the coordinates outside the largest face linearly to `0`, which
keeps every inequality; what remains is convex. By Leray's theorem the Čech complex of this
cover computes `H^*(S^(N-1))`, and the cover spectral sequence of `S^(N-1) x Y` has
`E_2 = H^*(S^(N-1)) ⊗ H^*(Y) = E_infinity`, with `F^(N-1) = H^(N-1)(S^(N-1)) ⊗ H^*(Y)`.

The components of the `N`-fold intersection are the chambers `(sigma, pi)`. Here
`sigma in {±1}^N` chooses the side of each node and `pi` orders the `|v_nu|`, largest first.
On that chamber

```text
W = G ⊕ L_(pi(1)),   ell_i = L_(pi(i+1)),   L_nu = L_(nu, sigma_nu),   x_nu := c_1(L_nu) = (alpha or beta) u_nu.
```

A component of an `(N-1)`-fold intersection, `T = [N] \ {s}`, is a wall. It contains
exactly two chambers:
- if `s < N`, the two orders of the `s`-th and `(s+1)`-th weights, which differ in `sign(pi)`;
- if `s = N`, the two sides of the smallest node, which differ in `prod sigma`.

Both get the same Čech sign from `delta`. So `phi(c) = sum_chambers sign(pi) prod(sigma) c(sigma, pi)`
kills coboundaries. It sends the indicator of one chamber to `±1`, so it is an
isomorphism `Ȟ^(N-1) -> Q`. It agrees up to one global sign with orientation, since
`sign(pi) prod(sigma)` is the determinant of the linear map taking the standard chamber
to `(sigma, pi)`. The script checks the wall count and this sign.

**Step 3 (the value).** By naturality of the spectral sequences, `e^* Omega` is the class
of the Čech cochain `(sigma, pi) -> omega(chamber)`, so under `H^(N-1)(S^(N-1)) ≅ Q`

```text
e^* Omega  =  ± sum_(sigma, pi) sign(pi) prod(sigma) (ch_(m_1)(G) + x_(pi(1))^(m_1)/m_1!) prod_(k>=2) x_(pi(k))^(m_k).
```

Sum over `sigma` first, one node at a time. For fixed `pi`, the term is a product of
factors each depending on one `sigma_(pi(k))`. The `ch(G)` term does not depend on
`sigma_(pi(1))` and cancels. What is left is `prod_k (p_k(alpha u) - p_k(beta u))` with
`p_k(x) = x^(m_k)`, at `u = u_(pi(k))`. Hence

```text
e^* Omega  =  ± (1/m_1!) prod_k (alpha^(m_k) - beta^(m_k)) · sum_pi sign(pi) prod_k u_(pi(k))^(m_k)
           =  ± (1/m_1!) prod_k (alpha^(m_k) - beta^(m_k)) · det[u_nu^(m_k)].
```

The monomials `prod_nu u_nu^(m_(pi^(-1)(nu)))` are distinct for distinct `pi`, because the
`m_k` are distinct. In `H^*(Y) = Q[u]/(u_nu^(j_nu + 1))` the alternant is therefore non-zero
exactly when some `pi` has `m_(pi^(-1)(nu)) <= j_nu` for all `nu`. That is the bijection
condition.

*Limit.* Any `omega' in H^*(U_full)` is a polynomial in the `ch_k(W)` and the `y_i`
(`U_full` fibres over the flag manifold with convex fibres). On a chamber,
`ch_k(W) = ch_k(G) + x_(pi(1))^k/k!`, so `omega'` becomes a sum of terms
`a(G) prod_k x_(pi(k))^(m_k)` with `m_k >= 0`. The same computation gives
`a(G) prod_k (alpha^(m_k) - beta^(m_k)) det[u_nu^(m_k)]`. This is `0` if some `m_k = 0`, or two
`m_k` coincide, or no admissible bijection exists.

**Step 4 (the model loop is homotopic to `e`).** Scaling `P_G` from `1` to `2` keeps the rank,
so it is a homotopy in `X`. Two admissible weight systems `w`, `w'` are joined by
`(1-t) w + t w'`. At every point some weight is positive, and at most one side of each node
is positive, since the neighbourhoods of opposite facets are disjoint. So the rank stays
in `[g+1, g+N]`.

**Step 5 (the boundary of `Q` is homotopic to `e`).** This is Step 5 of
`toms-two-sibling-depth-two-proof`, word for word, with the band `[g+1, g+N]`. Take
`0 < epsilon < 1/4`. Rørdam's lemma gives `(e - epsilon)_+ = x (Q - delta)_+ x^*`, and
`(e - epsilon)_+` is again of the model form. Put `z = (Q - delta)_+^(1/2) x^*`.
- The path `(1 - t) Q + t z z^*` has range `range Q` for `t < 1`.
- The rotation `Z_theta = [cos theta z ; sin theta e^(1/2)]` joins `z z^* ⊕ 0` to `0 ⊕ e`
  with constant non-zero spectrum.

All ranks stay between `rank e >= g + 1` and `rank Q <= g + N`. The inclusions
`X(n) -> X(2n)` respect the `U_k` and the flags. So `(Q|∂S)^* Omega = e^* Omega`.

**Step 6 (conclusion).** Suppose `rank Q >= g + 1` on all of `S x Y`. Then `Q` maps `S x Y`
to `X`, and `(Q|∂S)^* Omega` is restricted from `H^*(S x Y) = H^*(Y)`. Its image in
`H^*(∂S x Y)` lies in `1 ⊗ H^*(Y)`. That subspace meets `F^1` of the cover filtration only in
`0`, because a class `1 ⊗ y` restricts to `y` on each `U_k`-preimage (which contains a point
times `Y`). But `e^* Omega` is a non-zero element of `F^(N-1) ⊆ F^1`, by Step 3. This is a
contradiction, so `rank Q <= g` somewhere. On `∂S` the rank is at least `rank e >= g + 1`, so
the point is interior.

**Step 7 (corollaries).** For Toms's twists `alpha^m != beta^m` for every `m >= 1`, so any
distinct exponents work, and one takes `m = (1, ..., N)`, placed along sorted `j`. For
`alpha = -beta`, odd exponents give `alpha^m - beta^m = 2 alpha^m`. The window-box corollary
is the paragraph "Consequence" of `toms-two-sibling-swap-drops-add-to-depth-two`, with `N`
nodes in place of two. In the box every other pair of every node carries one slot, which
gives `G` of rank `N(R-1)`, and the facet slots give the `2N` lines. The upper band gives
`rank Q <= NR`. Square.
