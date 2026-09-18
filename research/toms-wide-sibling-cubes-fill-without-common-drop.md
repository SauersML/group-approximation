---
rg: 2
id: toms-wide-sibling-cubes-fill-without-common-drop
kind: claim
title: The width-N band space of positive matrices is (N^2+2N-2)-connected, so the sibling-cube data of N swap nodes force no common drop once N + 2 sum j_nu <= N^2 + 2N - 1, and at N^2 + 2N the only obstruction is the top-column alternant; for equal dimensions the drop is forced iff N <= j and fillable iff N >= 2j - 1
artifacts:
  - experiments/toms-band-connectivity-2026-09-17/band_e2.py
  - experiments/toms-band-connectivity-2026-09-17/filling_table.py
  - experiments/toms-band-connectivity-2026-09-17/results.json
distinct_from:
  toms-sibling-cube-swap-drops-add-to-depth-n: that proves the drop is forced when the dimensions admit N distinct exponents (N <= j for equal j) and notes that top-column classes vanish beyond; this proves the converse for every invariant at once, since the band space has no homotopy below degree N^2 + 2N - 1, and shows the top-column class is the complete obstruction one degree higher.
  toms-chern-swap-count-allows-depth-one-drops: that builds depth-one drops on one swap family; this builds staggered fillings of whole N-node cubes, on which no point drops to the common rank.
  untwisted-doubling-tower-has-a-nonconstant-continuous-rank: that fills with trivial twists; this fills with Toms's twists, but only when the cube is wide compared with the projective dimensions.
---

**Setting.** As in `toms-sibling-cube-swap-drops-add-to-depth-n`. Let
`Y = CP^(j_1) x ... x CP^(j_N)` and `S = [0,1]^N`. Let `e` be the boundary model on
`∂S x Y`: a common bundle `G` of rank `g` plus, near each facet, the line of that facet.
Let `X_(g,N)(n)` be the space of positive `Q in M_n` with `g + 1 <= rank Q <= g + N`.
Put `D = N^2 + 2N - 2` and `d = dim (S x Y) = N + 2 sum j_nu`.

**Theorem A (band connectivity).** For all `g >= 0` and `n >= g + 1`, the space
`X_(g,N)(n)` is `D`-connected. For `n` large, `H_(D+1)(X_(g,N); Z) = Z`, and rationally its
dual is the top-column class `Omega` of `toms-sibling-cube-swap-drops-add-to-depth-n`
(exponents a permutation of `1, ..., N`).

**Theorem B (wide cubes fill).** Suppose `d <= D + 1`. Then any continuous map from `∂S x Y`
to the band space extends over `S x Y`, whatever `G`, the twists `alpha`, `beta` and the
weights. In particular there is `Q in M_n(C(S x Y))_+` with `Q|(∂S x Y) = e` and
`g + 1 <= rank Q <= g + N` everywhere. Such a `Q` satisfies both hypotheses of the cube
theorem and never drops to rank `g`.

**Theorem C (the next degree).** Suppose `d = D + 2`, that is `sum j_nu = N(N+1)/2`. Then the
model `e` extends over `S x Y` inside the band exactly when
`prod_(k <= N) (alpha^k - beta^k) · det[u_nu^k]_(k, nu) = 0` in `H^*(Y)`. For Toms's twists
(`alpha^k != beta^k` for all `k`) this happens exactly when the multiset `{j_nu}` is not
`{1, 2, ..., N}`.

**Corollary (equal dimensions).** Let every `j_nu = j`, with Toms's twists.
- `N <= j`: the drop to `g` is forced (`toms-sibling-cube-swap-drops-add-to-depth-n`).
- `N >= 2j - 1`, except `(N, j) = (1, 1)`: a staggered filling exists. For `N >= 2j`
  this is Theorem B, since `2Nj <= N^2 + N - 1`. For `N = 2j - 1` it is Theorem C, since
  `(j, ..., j)` is not `(1, ..., N)`.
- Only `j + 1 <= N <= 2j - 2` is left open. This is empty for `j <= 2`, so `j = 1, 2` are
  settled completely. The first open case is `(N, j) = (4, 3)`.

For `alpha = -beta` the factor `alpha^2 - beta^2` is `0`, so Theorem C always fills once
`N >= 2`.

**What it kills.** No argument that uses only the two cube hypotheses (boundary
domination by the transported lines, and the upper rank band) can force a common drop
of `N` bottom-level siblings once `N >= 2 j_n - 1`. This holds for torsion invariants,
lower Mayer–Vietoris columns, K-theory and Steenrod operations, since the band space has
no homotopy in the relevant range. At the bottom level of Toms's tower `j_n = 2 d_n^2`, so
the `K/2` bottom siblings force nothing once `K/2 >= 4 d_n^2 - 1`. The `(2, 1)` case of the
brief is not torsion-obstructed: the band space is 6-connected integrally, and
`d = 6 <= 7`.

So depth `K/2` cannot come from a wide single-level cube. Any route to the firewall's jump
must either
- use nodes of several levels, where the dimensions are unequal and the Hall condition
  "`#{nu : j_nu <= J} <= J` for every `J`" of the cube theorem can hold for `N = K/2`, or
- use data beyond the two cube hypotheses, such as the trace-count constraints inside
  the box.

**Model test.**
- *`N = 1`.* `D = 1`, so `X = BU(g+1)` is `1`-connected with `H^2 = Z`. With `j = 1`,
  `d = 3 = D + 2` and `{j} = {1}`, so Theorem C says the path cannot be filled. This is the
  `ch_1` obstruction.
- *Agreement with the cube theorem.* The Hall condition forces `sum j_nu >= N(N+1)/2`, that
  is `d >= D + 2`. So Theorems B and C never contradict the forced cases. At `d = D + 2` the
  two criteria coincide.
- *Computation.* `band_e2.py` computes the Mayer–Vietoris `E_2` page. Over `Z` (Smith
  normal form), for `N = 1` (stable `g`) and for `N = 2, 3` with `g in {0, 1, 2, stable}`, it
  finds `E_2 = 0` in total degrees `1` to `D` and `Z` in degree `D + 1` (`2`, `7` and `14`).
  For `N = 4` with stable `g`, it computes ranks over `F_p` for
  `p in {2, 3, 5, 7, 11, 13, 1000000007}`. For every such `p` it finds `E_2 ⊗ F_p = 0` in
  total degrees `1` to `22` and `F_p` in `23`, at `E_2^(3,20)` (see `results.json`).

Proof: `toms-wide-sibling-cubes-fill-proof`. Internal derivation, unreviewed.
