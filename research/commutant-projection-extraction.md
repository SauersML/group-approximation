---
rg: 2
id: commutant-projection-extraction
kind: claim
title: Corner-invisible central unitaries in a matrix corona are trivial
distinct_from:
  corona-corner-detection-criterion: that claim is established and reduces the mechanism to this question; this claim is the residual operator-algebraic hole, stated without any group-theoretic hypothesis beyond centrality.
  commutant-no-growth: that claim bounds the growth of an asymptotic commutant; this one asks for projections inside the relative commutant.
  mf-invariant-corner-visibility: that claim may choose a convenient realization and concludes a trace gap in the corner; this one is quantified over every given corona representation, is restricted to a central element, and concludes an operator-norm localization. Only the "for every realization" form is usable against MF-ness.
---

Let `Q` be a norm matrix corona, `H` a countable group,
`Theta: H -> U(Q)` a homomorphism, `B = Theta(H)' cap Q` the relative
commutant, and `eps in Z(H)`.  Suppose

    ‖q Theta(eps) q - q‖_2 = 0   for every nonzero projection q in B,

each corner being given its own normalized trace.  Then `Theta(eps) = 1`.

Equivalently (contrapositive, after a bump function): if
`‖Theta(eps) - 1‖ >= delta > 0`, then there are a nonzero projection
`q in B` and `lambda in sp(Theta(eps))` with `|lambda - 1| >= delta` and
`‖(Theta(eps) - lambda) q‖` as small as one wishes.

This is the decisive sub-claim for a torsion-free mechanism.  Granting it,
`corona-corner-detection-criterion` clause 3 kills a central defect square
of **any** order, and the Kazhdan--Clifford architecture needs only a
torsion-free group carrying an infinite-order central mark
(`infinite-order-central-mark-group`).

## Ideas

**Known cases.**  True when `Theta(eps)` has finite spectrum — in
particular when `eps` has finite order, which is the existing theorem — and
more generally whenever `sp(Theta(eps))` is disconnected, since then the
separating projection already lies in `C*(Theta(eps)) <= B`.  True also,
with no spectral hypothesis whatever, when `eps` lies in a **normal
property-(T) subgroup** of the ambient group: the Kazhdan fixed-space
projection of that subgroup is the required commutant projection, and
normality is exactly what makes it invariant under the ambient image
(`normal-kazhdan-defect-non-mf`, machine-checked).  That case does not cover
a central mark on its own, since the cyclic group it generates is amenable
and never Kazhdan — but it does cover a mark sitting inside a larger normal
Kazhdan subgroup, and it is why the root's primary route no longer runs
through this claim at all.  By
`corona-corner-detection-criterion` clause 2 the only surviving
configuration is `sp(Theta(eps))` a connected arc through `1`, or the whole
circle, with all trace mass at `1`.  So the question is exactly: *can a
central unitary carry an operator-norm defect on a set of vanishing
normalized rank whose phase varies continuously down to `1`?*

**Why the naive models do not settle it.**  Two families must be beaten,
and each is beaten by a different projection.

- *Block model.*  `eps_n = 1_{d_n - m_n} oplus C_{m_n}` with `C_m` the
  clock unitary of order `m`, `m_n -> infinity`, `m_n / d_n -> 0`.  Here
  `eps` has infinite order, is at operator distance `2` from `1`, and is
  HS-invisible; the spectrum is a dense subset of the circle, so no
  spectral cut exists inside `C*(Theta(eps))`.  But the block projection
  `1_{m_n}` commutes with everything that commutes with `eps_n` blockwise
  and detects `eps` (its corner distribution is the uniform measure on
  `mu_{m_n}`).  So this model is not a counterexample — it shows only that
  the projection must be sought in `B`, not in `C*(Theta(eps))`.
- *Continuous-phase model.*  `eps_n = diag(e^{i theta_j})` with
  `theta_j = f_n(j/d_n)`, `f_n` vanishing on `[0, 1 - delta_n]` and rising
  to `pi`, with `delta_n -> 0` and `delta_n d_n -> infinity`; pair it with
  the cyclic shift `S_n`, which commutes with `eps_n` asymptotically
  because consecutive phase increments are `O(1/(delta_n d_n))`.  This is
  HS-invisible, at operator distance `2` from `1`, and every arc cut of
  `eps_n` fails to commute with `S_n` (a hard cut of an interval of
  positions has commutator norm `1` with the shift).  **This model has now
  been resolved, and it is not a counterexample.**  Take `d_n = n^2`,
  `delta_n = 1/n`, so the phase rises from `0` to `pi` across the last `n`
  positions in increments `pi/n`.  Fix `lambda = e^{i pi / 2}`, let `j_0` be
  a position where the phase is `pi/2`, and let `psi_n` be a smooth `l^2`-
  normalized bump of width `L_n = sqrt(n)` centred at `j_0`.  Then the phase
  varies by `L_n · pi/n = pi/sqrt(n)` across the bump, so
  `‖(eps_n - lambda) psi_n‖ -> 0`; and a smooth bump of width `L` satisfies
  `‖S_n psi_n - psi_n‖ = O(1/L_n) -> 0`, so the rank-one projection
  `q_n = |psi_n><psi_n|` satisfies `‖[q_n, S_n]‖ -> 0`.  In the ultraproduct
  `q` is a nonzero projection of the relative commutant with
  `eps q = lambda q` and `lambda != 1`: the corner exists.  So the sharpest
  test case falls on the side of the claim.

**But the technique that resolved it is unavailable here.**  The wave packet
is an approximate joint eigenvector, and the projection onto it has rank
one.  By `bounded-rank-corners-excluded`, a rank-one corner detecting the
mark forces a one-dimensional representation of the Kazhdan source, so it
cannot exist when that source is perfect; and no bounded-rank corner exists
when the source is minimally almost periodic, as the repository's
`St_5(L)` is.  The shift model escapes only because its group is abelian and
has characters to spare.  So a witness for this claim must have unbounded
rank while carrying no Kazhdan-invariant vectors and, by transport, zero
trace — which is a demanding combination, and is the sharpest current reason
to suspect the claim may fail for Kazhdan sources.  Anyone attacking it
should decide first whether to look for such a corner or for a
counterexample, because the two searches now have different shapes.

**Reduction to real rank zero of a relative commutant.**  This is the
sharpest form of the question, and the recommended next work unit.  Fix a
free ultrafilter and work in `A_omega = prod_omega M_{d_n}`, a quotient of
`Q`; corners of `A_omega` by projections are again norm ultraproducts of
matrix algebras, so the manuscript's transport applies in them verbatim.
Put `B_omega = tilde U(H)' cap A_omega`, which contains `tilde U(eps)`.
Then it suffices that

    her_{B_omega}(f(tilde U(eps)))  contains a nonzero projection

for a continuous bump `f` supported on an arc around a spectral point
`lambda != 1`: if `q` is such a projection and `g` is continuous with
`g f = f`, then `g(tilde U(eps)) q = q`, so
`‖(tilde U(eps) - lambda) q‖` is at most the width of the arc, and clause 3
of `corona-corner-detection-criterion` fires in the corner `q A_omega q`.
In particular **real rank zero of the relative commutant `B_omega` implies
the claim**.  Two remarks on the shape of an answer:

- `A_omega` itself has real rank zero — invertible self-adjoint
  approximation in `M_d` has a modulus independent of `d`, so the property
  passes to norm ultraproducts — and it is countably saturated, as is
  `B_omega` for countable `H`.  Countable saturation alone does not give
  real rank zero (ultrapowers of `C([0,1])` are countably saturated and
  projectionless in the relevant sense), so the question is genuinely about
  what a relative commutant inside a matrix ultraproduct can look like.
- Alternatively, a maximal abelian subalgebra `M` of `B_omega` containing
  `tilde U(eps)` suffices if `M` is a commutative AW*-algebra: then
  `M = C(X)` with `X` extremally disconnected, the closure of
  `{|eps - lambda| < eta}` is clopen, and its characteristic function is
  the required projection.  Whether masas of a matrix norm ultraproduct are
  AW* is the question to settle first; it is elementary to state and does
  not mention groups.

The (T) input is *not* what is missing here: the existing transport theorem
already produces an exact projection `P = V P V^*` in a finite ultraproduct,
but of the *adjoint* representation on Hilbert--Schmidt vectors, which is
why it controls only the `2`-norm.  See `coordinate-ultraproduct-transport`
for what the same argument gives on the coordinate ultraproduct.

**What must not be assumed.**  Voiculescu's almost-commuting unitaries show
that asymptotically commuting families need not admit any almost-invariant
spectral cut; the pair `(clock, shift)` has nonzero Bott index and no
nearby commuting pair.  Any proof must therefore use either the vanishing
of the trace mass off `1` or the (T) input, not general position.
`matrix-corona-k1-vanishes` rules out an index-theoretic invariant of the
mark alone.
