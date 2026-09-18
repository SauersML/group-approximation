---
rg: 2
id: toms-sibling-cube-swap-drops-add-to-depth-n
kind: claim
title: On the cube family of N twisted swap nodes, a Cuntz target that contains a common bundle plus the transported line of each face and has rank at most N above the common part drops to the common rank at an interior point, whenever the projective dimensions admit N distinct exponents; the invariant is an alternant, and it vanishes identically when they do not
artifacts:
  - experiments/toms-sibling-cube-2026-09-17/cube_invariant.py
  - experiments/toms-sibling-cube-2026-09-17/results.json
distinct_from:
  toms-two-sibling-swap-drops-add-to-depth-two: that is the case N = 2 with the degree-7 class c_1(W) y^2, which vanishes for alpha = -beta; this is every N, with the top-column class ch_(m_1)(W) y_1^(m_2) ... y_(N-1)^(m_N) over the cross-polytope, whose value is an alternant; odd exponents settle alpha = -beta, and the alternant shows exactly when no class of this kind can work.
  toms-chern-swap-count-allows-depth-one-drops: that builds depth-one drops on one swap family; this shows N such families over distinct nodes cannot be coordinated so that fewer than N of them drop at one point, within the stated dimension range.
  toms-swap-drop-locus-has-codimension-at-most-2m-plus-1: that bounds the dimension of the drop set on one node; this bounds the depth of the drop at one point across N nodes.
  untwisted-doubling-tower-has-a-nonconstant-continuous-rank: that realizes the rotation with trivial twists; there every factor alpha^m - beta^m of the invariant is zero.
---

**Setting.** Let `N >= 2` and `Y = CP^(j_1) x ... x CP^(j_N)`, with hyperplane classes
`u_1, ..., u_N`. For each node `nu` let `L_(nu,+)`, `L_(nu,-)` be line bundles pulled back
from the `nu`-th factor, with `c_1 = alpha u_nu` and `c_1 = beta u_nu`. Let `S = [0,1]^N`.
The facet `{s_nu = 1}` carries `L_(nu,+)` and the facet `{s_nu = 0}` carries `L_(nu,-)`.
Let `G` be a bundle of rank `g` on `Y`. Let `P_G` and `P_a` (one for each of the `2N` lines)
be mutually orthogonal projections in some `M_k(C(Y))` with these ranges. Put

```text
e = P_G + sum_a w_a(s) P_a   on  ∂S x Y,
```

where the weights `w_a >= 0` are continuous, `w_a = 1` on facet `a`, and `w_a` vanishes
outside a small neighbourhood of facet `a`. Opposite facets have disjoint neighbourhoods,
so near a face of codimension `k` exactly the `k` lines of its facets are present.

**Theorem (cube obstruction).** Suppose there are distinct integers `m_1, ..., m_N >= 1`
with `alpha^(m_k) != beta^(m_k)` for all `k`, and a bijection `k -> nu(k)` with
`m_k <= j_(nu(k))`. Let `Q in M_n(C(S x Y))_+` with
- `e <~ Q|(∂S x Y)`, and
- `rank Q <= g + N` on `S x Y`.

Then `rank Q(w) <= g` for some `w in S x Y`. Since `rank Q >= g + 1` on `∂S`, `w` is interior.

The obstruction lives in the space `X` of positive matrices with rank in `[g+1, g+N]`.
Cover `X` by `U_k = {lambda_(g+k) > lambda_(g+k+1)}`, `k = 1, ..., N`. On `U_1 ∩ ... ∩ U_N` the
flag `W_(g+1) ⊂ ... ⊂ W_(g+N)` of top eigenspaces is continuous. Put `W = W_(g+1)` and
`y_i = c_1(W_(g+i+1)/W_(g+i))`. The class `omega = ch_(m_1)(W) y_1^(m_2) ... y_(N-1)^(m_N)` sits
in the top column of the Mayer–Vietoris spectral sequence. It gives
`Omega in H^(N-1+2 sum m)(X)`. On the boundary map it evaluates to

```text
e^* Omega  =  ± (1/m_1!) prod_k (alpha^(m_k) - beta^(m_k)) · det[ u_nu^(m_k) ]_(k,nu)
           in  H^(N-1)(S^(N-1)) ⊗ H^*(Y).
```

The alternant is non-zero in `H^*(Y)` exactly under the bijection condition. For `N = 3` and
exponents `(1, 2, 3)` the value is
`-(alpha - beta)^3 (alpha + beta)(alpha^2 + alpha beta + beta^2) u_1 u_2 u_3 (u_1 - u_2)(u_1 - u_3)(u_2 - u_3)`.
It is non-zero once every `j_nu >= 3`.

**Corollaries.**
- *Toms's twists.* `O(1), O(2)` (or `alpha = -2`, `beta = -1`) have `alpha^m != beta^m` for all
  `m`. The condition becomes `j_(i) >= i` for the sorted dimensions. For equal
  dimensions `j` it is `N <= j`. Depth `N` is then forced at one point of every window box.
- *The case `alpha = -beta` is settled for large `j`.* Take odd exponents `1, 3, ..., 2N - 1`.
  Then `alpha^m - beta^m = 2 alpha^m != 0`, and the condition is `j_(i) >= 2i - 1`. For `N = 2`
  this needs `j >= 3`, where the class `ch_1(W) y^3` gives `± 4 alpha^4 (u_1 u_2^3 - u_1^3 u_2)`.
- *Window boxes.* Put the depth-one transport of `toms-chern-swap-count-allows-depth-one-drops`
  on `N` nodes, and take one widened window per node. The other pairs give `G`, with
  `g = N(R - 1)`, and the upper band gives `rank Q <= NR = g + N`. So `Q` drops by `N` at an
  interior point of the box, exactly as in the case `N = 2`.

**Limit (what no class of this kind can do).** Every class of the top column is a
polynomial in `ch(W)` and the `y_i`. On the boundary map its value is a sum of terms
`a(G) prod_k (alpha^(m_k) - beta^(m_k)) det[u_nu^(m_k)]`, with `a(G)` a fixed class. If no
system of distinct admissible exponents exists, every term is `0`. For Toms's twists this
happens as soon as `N > j` with all `j_nu = j`. At the bottom level of the tower there are
`K/2` sibling nodes, all with the same `j_n = 2 d_n^2`. So for `K > 4 d_n^2` this invariant
forces depth at most `j_n` from bottom-level nodes, not `K/2`. Passing to that depth needs
nodes of several levels, or an invariant outside the top column.

**Model test.**
- *`N = 1`.* The two ends of the interval carry `G ⊕ L_-` and `G ⊕ L_+`. The formula
  gives `(alpha^m - beta^m) u^m / m!`, the difference of `ch_m`, which is exactly why a
  constant-rank path between them cannot exist.
- *`N = 2`.* Exponents `(1, 2)` give `(alpha - beta)^2(alpha + beta)(u_1 u_2^2 - u_1^2 u_2)`.
  This is the value in `toms-two-sibling-swap-drops-add-to-depth-two`, up to sign.
- *Untwisted.* `alpha = beta` kills every factor. This is consistent with
  `untwisted-doubling-tower-has-a-nonconstant-continuous-rank`.
- *Product model.* The block-diagonal product of `N` depth-one models drops by `N` at a
  point, as the theorem requires.
- *Script.* The artifact checks the following for `N = 2, 3, 4`.
  - Every wall of the cover holds two chambers of opposite orientation, and the
    orientation agrees with the determinant of the barycentric simplex.
  - Classes from the next column give `0`.
  - The alternant formula holds for eight exponent systems.
  - A brute force over all top-column monomials, with free Chern classes of `G`, gives
    `0` for `(N, j) = (2, 1)` and `(3, 2)`, and for `alpha = -beta`, `(N, j) = (2, 2)`. It
    gives non-zero values for `(3, 3)`, and for `alpha = -beta`, `(2, 3)`.

**What it does not do.**
- It does not decide `N > j`. There the top column is blind, and a staggered filling
  might exist. A side computation, not used in the proof: for `N = 2` the band space is
  simply connected with rational cohomology `0` in degrees `1` to `6`. It is the homotopy
  pushout of `BU(g+1) <- BU(g+1) x BU(1) -> BU(g+2)`, and the Mayer–Vietoris cokernel starts
  with `c_1(W) y^2`. So for `(N, j) = (2, 1)`, where `S x Y` has dimension `6`, every
  obstruction to filling is torsion.
- It does not produce window boxes from a general approximant.

Proof: `toms-sibling-cube-depth-n-proof`. Internal derivation, unreviewed.
