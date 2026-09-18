---
rg: 2
id: toms-transit-windows-fill-unless-their-ranks-overlap
kind: claim
title: Every transit window of the pushforward of a Toms approximant has room more than one per node, so the ancestor cube theorem never applies to it directly; a box of windows whose leaf maxima do not overlap is filled at maximal constant rank with no drop, and overlap is exactly what forces a one-node drop
distinct_from:
  toms-ancestor-twisted-cubes-force-depth-k-over-2: that proves the drop for cube data with room one per node; this shows the pushforward of any approximant never offers room one, because lower semicontinuity and the upper band cost one rank at every transit, and replaces room by the overlap excess.
  toms-constant-rank-twisted-transport-costs-double-rank: that bounds a constant-rank target over a whole swap family; this localizes the count to a window, shows it is decided by the two leaf maxima on the window alone, and shows windows without overlap fill at constant rank.
  toms-chern-swap-count-allows-depth-one-drops: that builds depth-one drops on one family; this says which windows of a general approximant must contain a drop at all, and that the smallest such window transits two lines per leaf.
---

**Setting.** Work in Toms's non-simple limit `A` (Section 4 of arXiv:2606.12188v2), in
stage-`M` rank units. The statements for `B` are in the last paragraph. Let
`h in C(X_1)` be non-constant, `f(tau) = tau(h)`, and let `a_m` be Cuntz-increasing with
`d(a_m) <= f` and `eps_m = sup (f - d(a_m)) -> 0`. Fix `n < M` and `K = 2^(M-n)`.

A *node* `nu` is a pair of sibling copies `b, b'` of `X_n` in `X_M`, under a level-`(n+1)`
vertex `v` with factor `CP^(j_v)`, `j_v = j_n = 2 d_n^2`. Its copies carry the lines
`L_(nu,+) = gamma_(v,1) ⊗ Gamma_nu` and `L_(nu,-) = gamma_(v,2) ⊗ Gamma_nu`, with
`c_1 = alpha u_v + A_nu` and `beta u_v + A_nu`, where `alpha != beta` are both non-zero
(`toms-ancestor-twisted-cubes-force-depth-k-over-2`). Fix a *swap path* `x : [0,1] -> X_n`,
along which `phi = F_n ∘ x` is strictly increasing and `phi(s) + phi(1-s) = c` is constant.
On the node family copy `b` sits at `x(s)` and copy `b'` at `x(1-s)`, and all other
coordinates are fixed.

Put `R(s) = rank a_n(x(s))`, a lower semicontinuous integer function with
`R <= d_n phi`. The node block of `psi_(n,M)(a_n)` at `s` has support `R(s) L_+ ⊕ R(1-s) L_-`.
A *window* is an interval `I = [s_0, s_1]`. Put

```text
Pbar = max_I R(s),   Qbar = max_I R(1-s),   p* = min_I R(s),   q* = min_I R(1-s),
kappa(I) = Pbar + Qbar - d_n c            (the overlap excess).
```

The window *transits* if `Pbar > p*` or `Qbar > q*`. On a box `S = prod_nu I_nu` the common part
`G` of the pushforward (other copies, point data, and `p*_nu L_+ ⊕ q*_nu L_-` for each `nu`)
has rank `g`. The upper band on the box is the integer `U = floor(d_M f)`, which is
constant there, since `f` is.

**Theorem.**
1. *Room is more than one.* `R(s) + R(1-s) <= ceil(d_n c) - 1` for every `s`. So on a window
   that transits, `d_n c - p* - q* >= 2 - (ceil(d_n c) - d_n c) > 1`. A box of `N`
   transiting windows has `U - g > N`. Theorem 1 of
   `toms-ancestor-twisted-cubes-force-depth-k-over-2` asks for `rank Q <= g + N`. Any
   target with the lower band `rank >= U - d_M eps` meets that only if `d_M eps > U - g - N > 0`.
   With `N = K/2` single-jump windows and `d_n c` an integer, the premise is already
   `eps >= 1/(2 d_n)`, which is the conclusion. The step "extract room one per node" is
   circular. It is not a gap in the extraction.
2. *Windows without overlap fill.* If `kappa(I_nu) <= 0` for every `nu`, there is
   `Q_fill in M_infinity(C(S x Y x Z))_+` of constant rank `U` with `psi_(n,M)(a_n) <~ Q_fill` on
   the box. It meets every rank band that `a_M` meets. So no argument that uses only the
   explicit containment of the pushforward and the rank bands on such a box can force
   any drop. This covers every box of windows with one jump per leaf in the ideal case
   `R = floor(d_n phi)` with lower semicontinuous jumps and `d_n c` an integer, where
   `kappa = 0`.
3. *Overlap forces a drop on one node.* Suppose `N = 1`, `Q` is defined on `I x CP^(j_v)`
   (all other coordinates fixed), `psi_(n,M)(a_n) <~ Q`, and `rank Q <= g_0 + r`. Here
   `g_0` is the rank of the part of the pushforward outside the node, and
   `Pbar + Qbar > r` with `r <= j_v`. Then `rank Q < g_0 + r` somewhere on `I x CP^(j_v)`.
4. *Smallest forcing windows.* When `d_n c` is an integer and `kappa(I) >= 1`, the window
   gains and loses `(Pbar - p*) + (Qbar - q*) >= 4` lines, and has room
   `d_n c - p* - q* >= 3`. The ideal staircase achieves this with two walls: `2` gains,
   `2` losses, room `3`. Theorem 1's cube data (one line per facet, room one) is the
   pattern `(1, 1; 1)`, which no transit window of a pushforward has.
5. *Forcing windows exist.* If `eps_n + 1/(2 d_n) < phi(1/2 + w) - phi(1/2)`, the symmetric
   window `[1/2 - w, 1/2 + w]` has `kappa >= 1` at every node. Since `eps_n -> 0`, such
   windows exist for every large `n`, with the same `w` at all `K/2` bottom nodes.

**What it changes.** The brief's step asked for a target with room one per node inside
the chain `psi(a_n) <~ a_(M') <~ a_M`. Part 1 shows that this is equivalent to the
conclusion. Part 2 shows that single-jump boxes are genuinely unobstructed. The obstruction
therefore has to be a cube theorem for *overlap windows*, whose facets carry two lines each
and whose room is three (`toms-overlap-window-cubes-force-linear-depth`). Only a linear
depth `cN` is needed there, not depth `N`.

**Model test.**
- *Product model.* The block product of the depth-one transports of
  `toms-chern-swap-count-allows-depth-one-drops` over a forcing window drops by one at each
  node, as Part 3 requires. Over a single-jump window it can be replaced by the constant
  filling of Part 2, which does not drop.
- *Untwisted.* With `alpha = beta` Part 3 fails: `(1 + alpha u)^(Pbar + Qbar)` has too large a
  degree, but only one root is present, and the untwisted rotation realizes the transport
  (`untwisted-doubling-tower-has-a-nonconstant-continuous-rank`).
- *Theorem 1 at `N = 1`.* Room one with one line per facet has `kappa = 1`. Part 3 then
  reads `L_+ != L_-`, which is the case `N = 1` of the cube theorem.

**In `B`.** Point blocks are constant fields. They lie in `g_0` and are trivial on the slice
`CP^(j_v)`. Branch traces replace point traces, and `d_n` becomes `r_n / beta_n` in Parts 1
and 5 (`toms-simple-algebra-has-no-block-diagonal-rank-realizer`). The proofs are
unchanged.

Proof: `toms-transit-windows-fill-unless-overlap-proof`. Internal derivation, unreviewed.
