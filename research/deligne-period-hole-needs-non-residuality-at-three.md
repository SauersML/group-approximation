---
rg: 2
id: deligne-period-hole-needs-non-residuality-at-three
kind: claim
title: A metaplectic half-model shares every recorded invariant of a one-third model except exact untwistability, so residual-blind proofs of the period hole refute the flagship
distinct_from:
  finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres: that says finite equivariant Morita shifts cannot move LLP from the metaplectic fibre to an odd fibre; this builds an asymptotic (non-exact, non-residual in norm) half-model and uses it to calibrate every argument for the period hole, and says nothing about LLP.
  metaplectic-half-class-has-an-exact-finite-model: that gives an exact half-model; this tensors a growing family of such models with Dadarlat's winding model to get a half-model that is far from every exact projective representation and has regular traces, the features that the exact model lacks.
  deligne-maslov-tensor-functors-are-asymptotically-regular: that is a structural necessary condition on one-third models; this shows the same condition, and every other recorded one, is met at the half parameter, which always lies in P_op, so none of them can drive a proof of the period hole.
  deligne-parameter-group-is-a-virtual-invariant: that kills virtual descent at the step divide-by-three; this is a model-level calibration that isolates the same three-adic input (non-residuality of b mod 3) as the one ingredient any proof must use.
  deligne-finite-parameter-group-has-period-prime-to-three: that is the open period hole; this is a no-go for a class of proofs of it, not a proof or disproof.
---

**ESTABLISHED** (route `deligne-period-hole-needs-non-residuality-at-three-proof`).

**Setting.** `Gamma = Sp_4(Z)`. `b`, `E_infinity`, `E_q` and `P_op` are as in
`deligne-sep7-norm-parameter-closed-subgroup`. For `theta in R/Z`, a *`theta`-model* is a sequence of unital maps
`U_n : Gamma -> U(d_n)` with `||U_n(g)U_n(h) - e(theta b(g,h)) U_n(gh)|| -> 0` for every fixed pair; so
`theta in P_op` iff one exists. `r = prod_(i<=g) [a_i, b_i]` is a relator of `Gamma` whose hatted lift is
`zeta^k`, `k != 0` (Step 0 of `sp4-quasirep-windings-budget-and-saturation-proof`), and `kappa_r` is its winding.

**Invariants of a model `U` of class `theta`.**
- (I1) *Nontrivial class.* `theta != 0` has finite order `l >= 2`, and `U^(x l)` is an untwisted asymptotic
  homomorphism.
- (I2) *Central-regular traces.* `tr U_n(g) -> 0` for every `g not in {+I, -I}`. Hence, as in
  `deligne-maslov-tensor-functors-are-asymptotically-regular`, every tensor functor of `U` has regular trace, and
  `U` is at distance `>= 1` (normalized HS) from every bounded-level or finite-image comparison.
- (I3) *Unbounded dimension.* `d_n -> infinity`.
- (I4) *Not residual in norm.* `U` is not asymptotically close (pointwise operator norm distance `-> 0`) to any
  sequence of exact projective representations of class `theta`.
- (I5) *Carries winding after untwisting.* Some honest-class tensor functor of `U` with one exact factor, for
  example `conj(E_n) (x) U_n` with `E_n` exact of class `theta`, has `kappa_r != 0`.
- (X) *Exact untwistability.* Some exact finite-dimensional projective representation of class `-theta` exists.
  Equivalently, `theta b mod Z` lies in the image of the residual (profinite) classes.

**Theorem.**
1. Every `1/3`-model satisfies (I1)--(I4), and fails (X). (I1) holds with `l = 3`. (I2) is
   `deligne-maslov-tensor-functors-are-asymptotically-regular`. (I3) and (I4), and the failure of (X), come from
   `deligne-triple-cover-fd-central-invisibility`: no exact projective representation of class `1/3` or `2/3`
   exists. (I5) is vacuous for `1/3`.
2. There is a `1/2`-model `M_n = W_n (x) D_n` that satisfies (I1)--(I5) and (X). Here `W_n` is the exact
   metaplectic model cut from the regular representation of a separating chain of finite quotients of `E_2`, and
   `D_n` is Dadarlat's asymptotic homomorphism with `kappa_r(D_n) != 0`. Concretely:
   - `kappa_r(conj(W_n) (x) W_n (x) D_n) = (dim W_n)^2 kappa_r(D_n) != 0`;
   - for every exact projective half-representation `rho` on the same space,
     `max_(y in {a_i, b_i}) ||M_n(y) - rho(y)|| >= 1/(2g) - o(1)`;
   - every tracial limit of `M` is the average of the two central-regular traces.
3. **Calibration.** Call an argument for "`1/l in P_op` implies `P_op = R/Z`" *residual-blind* if it uses of the
   model only (I1)--(I5), the value of `l` only through (I1), and of `Gamma` only facts true at both `l = 2` and
   `l = 3`. Every residual-blind argument, run at `l = 2` on `M`, proves `P_op = R/Z`, because `1/2 in P_op`
   always. So it proves `1/3 in P_op`, that `E_3` is MF, and the negation of
   `deligne-triple-cover-exact-mf-radical`. It also refutes the co-prerequisite `sp4-quasirep-windings-are-sublinear`
   of route `deligne-triple-cover-via-sublinear-windings`.

**What this changes.**
- The class killed, as proofs of the period hole on a flagship route, is every residual-blind argument: stability,
  rigidity, trace, winding and dimension-growth arguments that read only (I1)--(I5).
  - The invariant is exact untwistability (X), i.e. whether `theta b` is a profinite (residual) class. By Deligne,
    `b mod 2` is residual and `b mod 3` is not.
  - The step where every member dies is the substitution `l = 2`, which applies to `M`.
- Relation to earlier kills.
  - The w12 bounded-level class reads only (I2). Its obstruction holds for `M` exactly as for `1/3`-models.
  - The w8 virtual-descent argument does use the prime `3`, and it died at the three-adic step "divide by 3".
  - This node does not re-derive the w13 monomial kill, which is 3-specific (blocks of size divisible by `3`).
- A proof of the period hole must use, at one essential step, the failure of (X) at `3`: Deligne's theorem that
  the finite residual of `E_infinity` is `2Z` and not `Z`, or an equivalent three-adic input. The winding/trace
  information of a hypothetical `1/3`-model can only enter together with that input.
- The survivors are arguments that exploit (X) failing in a quantitative, asymptotic form. An example is: "every
  `1/3`-model is uniformly far from every `E (x) V` with `E` exact of any class and `V` untwisted". Such a bound
  is false at `1/2` by construction of `M`. This is where a surviving proof must live.
