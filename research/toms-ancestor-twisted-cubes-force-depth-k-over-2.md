---
rg: 2
id: toms-ancestor-twisted-cubes-force-depth-k-over-2
kind: claim
title: With the ancestors' projective factors included, the sibling cube of any N bottom swap nodes forces a common drop of depth N, because the ancestor twists turn the alternant into a Vandermonde in the ancestor classes; in Toms's tower all K/2 bottom siblings qualify, which is the firewall's depth
artifacts:
  - experiments/toms-ancestor-cube-2026-09-17/ancestor_cube.py
  - experiments/toms-ancestor-cube-2026-09-17/results.json
distinct_from:
  toms-sibling-cube-swap-drops-add-to-depth-n: that puts the facet lines on the product of the nodes' own factors, where the value is prod (alpha^m - beta^m) det[u^m] and needs the Hall condition, so N <= j for equal dimensions; this adds the ancestors' factors, over which the facet lines carry the common path twists A_nu, and the value det[(alpha u + A)^m - (beta u + A)^m] contains (alpha - beta)^N N! prod u_nu Vandermonde(A_nu), non-zero for every N.
  toms-wide-sibling-cubes-fill-without-common-drop: that fills the cube over S x prod CP^(j_nu) once N >= 2j - 1; this shows those fillings never extend over the ancestor directions, so in Toms's tower the loophole closes and depth K/2 is forced by bottom-level nodes alone.
  toms-chern-swap-count-allows-depth-one-drops: that builds depth-one drops on one node; the ancestor twist cancels in Hom(L_(nu,-), L_(nu,+)), so those models extend over the ancestors, and the obstruction here lives only in carries between different siblings.
---

**Setting.** Take the cube data of `toms-sibling-cube-swap-drops-add-to-depth-n`: nodes
`nu = 1..N` with factors `CP^(j_nu)` and classes `u_nu`, `S = [0,1]^N`, a common bundle `G` of
rank `g`, and facet lines `L_(nu,+)` on `{s_nu = 1}` and `L_(nu,-)` on `{s_nu = 0}`. Add a second
parameter space `Z`, a product of projective spaces `CP^(j_rho)` with classes `u_rho`, and let the
lines live on `Y x Z`, `Y = prod_nu CP^(j_nu)`, with

```text
c_1(L_(nu,+)) = alpha u_nu + A_nu,     c_1(L_(nu,-)) = beta u_nu + A_nu,     A_nu in H^2(Z).
```

Let `e = P_G + sum_a w_a P_a` on `∂S x Y x Z` as before.

**Theorem 1 (ancestor-twisted cube).** Let `Q in M_n(C(S x Y x Z))_+` with `e <~ Q` on
`∂S x Y x Z` and `rank Q <= g + N`. Suppose `alpha != beta`, every `j_nu >= 1`, and the
Vandermonde `V(A) = prod_(nu < nu') (A_(nu') - A_nu)` is non-zero in `H^*(Z; Q)`. Then
`rank Q(w) <= g` at some interior point `w`.

The top-column class `Omega` with exponents `(1, 2, ..., N)` is the rational fundamental
class of the band space (degree `N^2 + 2N - 1`). Its boundary value is

```text
e^* Omega = ± det[ (alpha u_nu + A_nu)^k - (beta u_nu + A_nu)^k ]_(k, nu = 1..N),
```

whose component of `u`-multidegree `(1, ..., 1)` is
`± N! (alpha - beta)^N u_1 ... u_N · V(A)`. No Hall condition on the `j_nu` is needed.

**Theorem 2 (the Vandermonde in a tree).** Let the nodes be leaves of a rooted tree whose
internal vertices `rho` carry the factors of `Z`. Let `A_nu = sum_(rho above nu) eps_(rho,nu) u_rho`,
where `eps_(rho,nu)` is `alpha` or `beta` according to the child of `rho` on the path to `nu`.
Let `a_rho b_rho` be the number of pairs of nodes whose last common ancestor is `rho`. If
`j_rho >= a_rho b_rho` for every `rho`, then `V(A) != 0`. Its leading monomial, in the order where
higher vertices are larger, is `prod_rho u_rho^(a_rho b_rho)`, with coefficient `± (alpha - beta)^(N(N-1)/2)`.

**Corollary (Toms's tower).** In `A` (Section 4 of arXiv:2606.12188v2), fix `n < M` and
`K = 2^(M-n)`. At stage `M` the block of a level-`n` node `nu` is twisted by the tensor
product of the lines `gamma_(rho,1)` or `gamma_(rho,2)` of its ancestors. So on the family
`F = [0,1]^(K/2) x P`, with `P` the product of all internal factors of `X_M`, the facet lines
have exactly the form above. A level-`(n + l)` ancestor has `a_rho b_rho = 4^(l-1)` and
`j_rho = 2 d_(n+l)^2 = 2 · 4^l d_n^2`. Theorem 2 applies with a factor `8 d_n^2` to spare.
- Every window box of the `K/2` bottom siblings (the cube data of the depth-one
  transports, extended over `P`) forces a drop of depth `K/2` at one point of `F`. In
  stage-`M` units that is the firewall's jump `K/2`, of trace `1/(2 d_n)`.
- In `B` the top blocks of `psi_(n,M)` come from the telescoped Section 4 diagonal map and
  carry the same ancestor twists. Point blocks are constant and enter `G`. The same
  depth `K/2` is forced, of trace `beta_n/(2 r_n)`.

**What it changes.** `toms-wide-sibling-cubes-fill-without-common-drop` built staggered
fillings of the cube over `S x Y` once `N >= 2 j - 1`. Restricted to a slice
`S x Y x {z}` the Vandermonde dies, so those fillings exist slice by slice, but they never
extend over the ancestor factors. A staggered filling has to carry support from one
sibling's line to another's. That carry is a section twisted by `A_nu - A_(nu')`, which is
`(alpha - beta) u_rho` plus lower terms at the last common ancestor `rho`. The Vandermonde is
the product of these classes. The single-level route is therefore not dead. What the
previous lane read as a limit of bottom-level cubes was a limit of cubes that forget the
ancestor directions.

**Weighting (the brief's question).** A level-`r` node sits in exactly one block of
`psi_(r+1,M)`. So a drop of one rank in its window costs one stage-`M` rank, `1/d_M` in `A` and
`beta_M/r_M` in `B`, at every level. Higher-level nodes give no extra weight per node.
Cubes that use nodes of several levels as directions, with facet lines from the nodes'
own factors only, need the Hall condition `#{nu : j_nu <= J} <= J`. With `a_l` nodes at level
`n + l`, that condition is `sum_(l' <= l) a_(l') <= 2 d_n^2 4^l`. With `a_l <= K/2^(l+1)` it gives
`N <= C (d_n K)^(2/3) = o(K)`. So the multi-level route of the brief could not reach `K/2`. The
ancestor factors enter as cohomological room, not as cube directions.

**Model test.**
- *Untwisted.* `alpha = beta` kills every entry, as in
  `untwisted-doubling-tower-has-a-nonconstant-continuous-rank`.
- *No ancestor twist.* `A_nu = 0` gives back the old alternant, which vanishes when Hall
  fails. The script confirms `0` for `N = 2, 4` with `j = 1` and for `N = 4` with `j = 3`.
- *Product model.* The depth-one transport of one node uses `Hom(L_(nu,-), L_(nu,+))`, in which
  `A_nu` cancels. So the block product of depth-one models extends over `Z` and drops by
  `N` at a common point, as Theorem 1 requires.
- *Computation.* `ancestor_cube.py` checks, symbolically, that the chamber sum over
  `(sigma, pi)` equals `(1/m_1!) det[x_+^(m_k) - x_-^(m_k)]` with free `x` and `ch(G)`, for
  `N = 2, 3` and four exponent systems. It computes the full determinant in the truncated
  ring for `N = 2, 4`, `j_nu in {1, 2, 3}`, twists `(1, 2), (-1, -2), (-2, -1), (1, -1)` and the
  minimal room `j_rho = a_rho b_rho`, and finds it non-zero in every case. This includes
  `(N, j) = (4, 3)`, left open over `S x Y`. It computes `V(A)` for `N = 2, 4, 8`, where at
  minimal room it is the single top monomial.

**What it does not do.** It does not produce the window-box data from a general
Cuntz-increasing approximant. The upper band per node is the issue. An ideal `a_n` has
rank `floor(d_n F)` along the swap path, so the node block of `psi(a_n)` has deficiency `1`
off the jump points and `2` at them. `a_M` then has room `2` per node at a transit point,
while Theorem 1 needs room `1`. The next step is to extract, inside the chain
`psi(a_n) <~ a_(M') <~ a_M`, a target with room one per node on a box. Theorem 1 then gives
`eps_M >= 1/(2 d_n)`.

Proof: `toms-ancestor-twisted-cubes-proof`. Internal derivation, unreviewed.
