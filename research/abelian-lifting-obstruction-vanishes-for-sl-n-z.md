---
rg: 2
id: abelian-lifting-obstruction-vanishes-for-sl-n-z
kind: claim
title: The bounded second cohomology of SL_N(Z) with coefficients in the trace-null ideal vanishes, so the abelianized lifting obstruction is zero
distinct_from:
  tracial-to-uniform-lifting-for-sl-n-z: that is the nonabelian lifting of representations through the trace-null ideal; this is its ABELIANIZED shadow -- vanishing of H^2_b(Gamma, I) -- which is proved here from Ulam-stability cohomology plus property (T), and which is necessary but, because the ideal is not nilpotent, not sufficient.
  bounded-degree-two-primitives-for-higher-rank-lattices: that asked for operator-bounded primitives of 2-norm-small cocycles; this shows the operator-bounded primitive of an I-valued bounded cocycle can be taken I-valued, by a degree-one (T) correction -- the ideal version, which is what lifting actually needs.
---

Let `Gamma = SL_N(Z)`, `N >= 3`, `A = prod_U^(op) M_(d_m)` the
operator-norm ultraproduct with the Ad-action of a lift of a
representation `pi : Gamma -> U(A/I)`, and `I` the trace-null ideal
(a closed two-sided Ad-invariant Banach `Gamma`-submodule).  Claim:

```text
H^2_b(Gamma, I) = 0
```

(bounded cohomology: cochains bounded in operator norm).
Consequently the defect 2-cocycle of any bounded set-theoretic lift
of `pi` is the coboundary of a bounded 1-cochain WITH VALUES IN `I`.

PROOF.  The short exact sequence `0 -> I -> A -> A/I -> 0` of Banach
`Gamma`-modules gives the long exact sequence
`H^1_b(Gamma, A) -> H^1_b(Gamma, A/I) -> H^2_b(Gamma, I) ->
H^2_b(Gamma, A)`.  The last group vanishes: this is the
asymptotic-cohomology vanishing of Glebsky--Lubotzky--Monod--
Rangarajan [arXiv:2301.00476] behind uniform stability of high-rank
lattices in submultiplicative norms (Burger--Ozawa--Thom for
`SL_n(Z)`, `n >= 3`).  The middle map is onto its image by
exactness, so it suffices that `H^1_b(Gamma, A/I) = 0`: a bounded
1-cocycle `b : Gamma -> M = A/I` for `Ad pi` is, in the Hilbert
space `L^2(M)`, a cocycle of a unitary representation of a
Kazhdan group, hence `b = delta w` with `w in L^2(M)` the fixed
point of the affine isometric action; `w` lies in the closed convex
hull of the orbit `{b(g)}`, which is bounded in operator norm
uniformly in `g` (bounded cochain), and the operator norm is lower
semicontinuous on 2-norm limits of bounded sets, so `w in M` with
`|| w ||_op <= sup_g || b(g) ||_op`.  Hence the connecting map is
zero and `H^2_b(Gamma, I) = 0`.  Unwinding: if `y in C^1_b(Gamma, A)`
has `delta y = c in Z^2_b(Gamma, I)`, then `y mod I` is a bounded
1-cocycle into `M`, equal to `delta w`; lifting `w` to `tilde w in
A` with the same operator norm, `y' = y - delta tilde w` is
I-valued with `delta y' = c`.  QED.

## Attempts

- **What this does and does not give.**  It kills the
  obstruction to lifting TO FIRST ORDER: the corrected generator
  lifts `(1 + y'(s)) u_s` satisfy the relators up to the quadratic
  terms `y'(s) . Ad(u_s) y'(t)`, which lie in `I . I = I` -- still
  trace-null (good) but of operator norm `O(1)` (no gain).  Because
  `I` is not nilpotent and has no filtration by ideals with
  shrinking products, successive approximation does not converge;
  the honest residue is nonabelian.  Contrast with the Ulam regime,
  where the cocycle is operator-SMALL and quadratic terms are
  negligible -- that is precisely why GLMR's vanishing yields
  stability there and only this abelian statement here.
- **The nonabelian core as a fixed-point problem.**  Let `S` be the
  set of bounded maps `phi : Gamma -> U(A)` lifting `pi`.  The
  formula `(h . phi)(g) = phi(gh) phi(h)^(-1)` defines a `Gamma`-
  action on `S` (a torsor over the nonabelian group of maps into
  `N = U(A) cap (1 + I)`), and its FIXED POINTS are exactly the
  homomorphic lifts.  With the bi-invariant metric
  `|| u - v ||_2` on `N` and the sup-metric on `S`, the action is
  2-Lipschitz with all orbits bounded (diameter `<= 2`) -- a
  Kazhdan-type fixed-point theorem for Lipschitz actions on bounded
  POSITIVELY curved spaces (unitary groups in the 2-norm are
  sphere-like, not CAT(0)) would finish; none is known, and the
  positive curvature is the precise reason the circumcenter
  argument that works in degree one (affine isometric actions on
  Hilbert space) does not apply.  This is the sharpest statement
  the lane has of what HS-stability of a Kazhdan group actually
  requires beyond Ulam stability.
