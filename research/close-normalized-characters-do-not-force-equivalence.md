---
rg: 2
id: close-normalized-characters-do-not-force-equivalence
kind: claim
title: Finite-dimensional representations with normalized characters o(1) apart need not be equivalent
invalidates:
  - subgroup-exact-outliers-route
distinct_from:
  subgroup-exact-outliers-do-not-exist: that is the flexible correctability statement for almost-representations exact on a finite-index subgroup, which this does not refute; this refutes the lemma its route used to manufacture EXACT unitary equivalences between the coset-twisted restrictions.
  approximate-gram-data-certifies-only-inverse-square-dimension: that bounds what approximate inner products can force about dimension; this is the elementary observation that integrality of multiplicities gives nothing once the dimension grows, aimed at one specific proof step.
---

Let `Q_m` be finite groups, `d_m -> infinity`, and let `pi_m`, `pi'_m` be
unitary representations of `Q_m` on `C^(d_m)`.  The statement

> "two genuine finite-dimensional representations at distance `o(1)` in
> trace character are equivalent for large `m` (characters are integers
> against each irreducible block; a vanishing difference is eventually
> zero)"

is FALSE.  Integrality gives only `|m_tau - m'_tau| . dim tau <= eps_m d_m`
for each irreducible `tau` when the normalized characters are uniformly
`eps_m`-close, and `eps_m d_m` need not tend to zero.

**Counterexample in the setting of `subgroup-exact-outliers-route`.**  Let
`Q_m = SL_3(Z/N_m)`, `g in SL_3(Z)` a coset representative acting on
`Irr(Q_m)` by the (generally outer) automorphism `Ad(g-bar)`, and pick an
irreducible `tau_m` of dimension `<= eps_m d_m` whose `Ad(g-bar)`-orbit is
nontrivial, with `eps_m -> 0`.  Put `pi_m = pi_0 (+) tau_m` with `pi_0`
`Ad(g-bar)`-invariant of dimension `d_m - dim tau_m` (for instance a
multiple of the regular representation).  Then `pi_m` and
`pi_m o Ad(g)` have normalized characters within `2 eps_m` of each other
and the same kernel, yet are inequivalent for every `m`: the constituent
`tau_m` of `pi_m` is replaced by `tau_m o Ad(g)` in `pi_m o Ad(g)`.

**Consequence for the invalidated route.**  Step 2 of
`subgroup-exact-outliers-route` concludes "so exact unitary equivalences
exist" between `sigma_m|_(Lambda_0)` and `sigma_m|_(Lambda_0) o Ad(g_i)`
from exactly this lemma.  What the (T)-estimate actually yields is a
partial-isometry intertwiner with co-support `O((eta_m/eps_0)^2)`, i.e.
agreement of multiplicities only up to `o(d_m)` weighted mass -- the
regime of the counterexample.  Steps 3-4 then build on an exact
equivalence that need not exist (simultaneous invariance of the cut
corners under the `n` partial isometries is never addressed, and the
"Ostrowski-type vanishing" for `U(C_m)`-valued cocycles is not a theorem:
`H^2(Z/2 x Z/2, T) = Z/2` already with trivial action).  Hence the route
is invalid and `subgroup-exact-outliers-do-not-exist` is OPEN; the
claim itself is not refuted -- the counterexample representation is
itself within `O(sqrt(eps_m))` of a genuine representation obtained by
replacing `tau_m` with an invariant block of the same dimension.
