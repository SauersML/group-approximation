---
rg: 2
id: toms-schubert-algebra-has-a-non-constant-continuous-rank
kind: claim
title: Toms's no-Gamma AH algebra has a positive element whose rank function is finite, continuous and non-constant
distinct_from:
  toms-schubert-algebra-continuous-ranks-are-constant: that is the opposite rigidity conjecture, that every continuous rank in B is constant; this is its negation, the constructive side.
  toms-schubert-algebra-misses-a-rank: that asks for one unrealized continuous affine function; this asks only for one realized non-constant one, which all ranks occurring would give and which does not by itself give all ranks.
  doubling-ah-finite-stage-continuous-ranks-are-constant: that proves constancy for finite-stage elements and orthogonal sums of them; this asks for a genuine Cuntz supremum that escapes it.
refuted_by:
  - toms-schubert-algebra-continuous-ranks-are-constant
---

**OPEN.** Let `B` be Toms's simple AH algebra without uniform property Gamma
(arXiv:2606.12188v2, Proposition 4 and Theorem 5). Some `a in (B tensor K)_+`
has `tau -> d_tau(a)` finite, continuous and non-constant on `T(B)`.

This is the negation of `toms-schubert-algebra-continuous-ranks-are-constant`.
All ranks occurring in `B` implies it, since `T(B)` is the Poulsen simplex
(`toms-doubling-ah-trace-simplex-is-poulsen`). The converse is not claimed.
The non-simple limit `A` of Toms's Section 4 is the cleaner test case.

## Attempts

- **What a realizer must do pointwise.**
  `cuntz-sups-with-continuous-rank-converge-uniformly`: if `a = sup a_n` with
  finite-stage `a_n` and `d(a) = f` continuous, then `d(a_n) -> f` uniformly. At
  branch traces this is a fibre-rank bound
  `f(sigma_y) - eps <= beta_M rank(a_n)(y)/r_M + c <= f(sigma_y)` at **every**
  `y in X_M`, for every deep `M`. So a construction must kill the oscillation of
  fibre ranks at every point, not only their average.
- **Dead: additive increments (oscillation form of the firewall).** Leaf maps
  are coordinate projections of a product, so the fibre rank of a pushforward
  `psi_(k,M)(b)` has oscillation `sum_l omega_b(lambda_l(y))` at `y`, where
  `omega_b(x) = limsup_(z -> x) rank b(z) - rank b(x)`. Put all leaf coordinates
  at one point `x_0` of maximal oscillation: the normalized oscillation is at
  least `beta omega_b(x_0) / r_k` at every later stage. If each approximant is
  the pushforward of the previous one plus an increment whose fibre rank adds
  (an lsc integer function, e.g. an orthogonal summand), oscillation can only
  grow, while the uniform bound above forces it to `0`. So every approximant has
  continuous, hence constant, fibre rank. This recovers
  `doubling-ah-finite-stage-continuous-ranks-are-constant` for orthogonal
  increments. It also kills point-evaluation "room": the fresh trivial blocks of
  `psi^pt` have normalized mass `1 - alpha_n >= 1/(M_n + t_n)`, far above the leaf
  granularity `1/|L_(m,n+1)|`, but filling them adds rank additively.
- **Dead: spectral cuts with leaf-path offsets.** Let `h in C(X_m)` and let
  `u(l) in [0,1]` be the binary expansion of the leaf path `l`. The commutative
  design `R(l, path) = 1{h(x_m(path)) > u(l)}` has expectation `tau(h)` for every
  trace in which the leaf coordinate is independent of the stage-`m` point. That
  fails: by free leaf labels, some `mu_N = delta_y` puts `h(lambda_l(y))` at the
  midpoint of the dyadic cell of `l` for every `l in L_(m,N)`. The limiting
  trace charges `{h(x_m) = u(l)}`, the boundary of the support, so `d` is
  discontinuous there. In the stage-`N` leaf picture the point `y_N` is
  independent of the digits appended up to stage `N`, but not of later digits.
  Containment `psi(a_N) <= a_(N+1)` forces the value along a leaf to be read at
  the leaf's own ancestor, which depends on exactly the digits the adversary
  controls. Whether every leaf-block-diagonal realizer is dead is not settled.
- **Where a realizer must go (heuristic).** The two dead designs leave
  overlapping increments that rotate support between leaf blocks. At a point
  where old pieces switch off, the new approximant keeps its rank by carrying a
  direction from a sibling block. Between twisted blocks these carries are
  sections of Hom bundles with nonzero Euler classes over independent `CP`
  factors, so all can fail at one common point (the fuzz-persistence heuristic
  of the rigidity conjecture). The operator-containment scheme heals boundary
  drops only if the slack near simultaneous boundary crossings exceeds about one
  stage-`m` piece per leaf, which is the granularity of the first approximant.
  Next: carries weighted by continuous functions that vanish where their
  sections degenerate, so failed carries cost trace but not rank.
