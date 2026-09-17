---
rg: 2
id: stw99-problem-xl-amenable-actions-exact-groups
kind: claim
title: Every exact nonamenable group acts amenably on a unital stably finite classifiable algebra (STW Problem XL)
root: true
distinct_from:
  amenable-action-invariant-trace-forces-amenability: that established theorem says such actions preserve no trace and fix no measure on T(A); it constrains but does not decide this existence question, which asks whether the surviving Poulsen-type targets actually occur.
artifacts:
  - research/artifacts/stw99-presentations-cartan-cluster-2026-08-30.md
---

**Problem XL of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Does
every countable discrete exact non-amenable group act amenably on a
unital stably finite classifiable C\*-algebra?  (Exactness is
necessary: amenable actions on nuclear algebras force exactness.
Kirchberg-algebra analogues exist — Szabo's equivariant `O_∞`-stability
covers amenable actions of non-amenable groups on Kirchberg algebras —
and every exact group acts amenably on some compact space, but those
crossed products are traceless or non-simple/non-classifiable.)

## Attempts

* The weaker question with only a unital separable nuclear target and no
  invariant trace is now exact
  (`stw40-unital-nuclear-no-trace-iff-exact`).
  For a countable nonamenable group `G`, such an amenable action exists if
  and only if `G` is exact, and one may take `A=C(X)` for a compact metrizable
  amenable `G`-space.  Any invariant probability measure on `X` would
  integrate the topological-amenability witnesses to a Reiter net, so none
  exists.  Conversely, amenability plus nuclearity makes `A crossed_r G`
  nuclear and its canonical copy of `C*_r(G)` exact.  Thus arbitrary
  nonexact countable nonamenable groups are genuinely excluded; what remains
  in Problem XL is the simple stably finite classifiable realization, not
  existence of a unital nuclear trace-free model.
* Hard constraint established this session
  (`amenable-action-invariant-trace-forces-amenability`): the action
  can preserve no trace, and the affine action on `T(A)` can carry no
  invariant measure.  So candidate targets are pinned: `T(A)` must
  admit a measure-fixed-point-free affine action of `G`.  The Poulsen
  simplex is a natural candidate, and stably finite classifiable algebras
  with Poulsen trace simplex exist in abundance, so the obstruction does not
  close the problem; it dictates the shape of any construction: an amenable
  `G`-action on a classifiable algebra whose trace dynamics contain a
  boundary inside `T(A)`.
  The natural candidate is a classifiable model of a boundary action
  (crossed-product-by-hyperbolic-boundary data made stably finite via
  orbit-breaking in the sense of Deeley--Putnam--Strung), where
  amenability of the original boundary action should persist to the
  broken groupoid; nothing of this kind is in the literature.
* The trace obstruction is stronger than absence of a fixed point.
  By `stw40-trace-action-has-no-equicontinuous-island`, no nonempty
  invariant weak-star compact subset of `T(A)` can carry equicontinuous
  `G`-dynamics: closing the action to a compact group and Haar-averaging an
  orbit would produce an invariant probability measure, whose barycenter is
  an invariant trace.  Thus finite, profinite, compact-rotation, and all
  other equicontinuous trace models are excluded.  Any witness must realize
  genuinely non-equicontinuous boundary-type dynamics on every invariant
  compact trace subsystem.
* In fact boundary dynamics are forced, not merely suggested
  (`stw40-trace-simplex-contains-a-nontrivial-boundary`).  Choose a minimal
  compact convex invariant subset `C` of `T(A)`.  The closure of `ext(C)` is
  a nontrivial minimal strongly proximal `G`-space: minimality follows by
  taking closed convex hulls, while strong proximality follows by applying
  the barycenter map to probability measures and using extremality twice to
  remove convex combinations.  Thus every solution of XL must contain a
  genuine `G`-boundary inside its trace simplex.  The remaining problem is
  precisely to realize such forced boundary dynamics by an amenable action
  on a stably finite classifiable algebra.
* The forced boundary is itself topologically amenable
  (`stw40-trace-simplex-boundary-is-topologically-amenable`).  Amenability of
  the C-star action passes to the induced state-space action and then to the
  closed invariant boundary inside `T(A)`.  Therefore an XL witness does not
  merely contain abstract boundary dynamics: it contains an amenable
  boundary, exactly matching the compact model in the preceding reduction.
  The unresolved lift is from this commutative amenable boundary model to a
  unital simple stably finite classifiable algebra while preserving full
  C-star amenability (tracial amenability alone is known not to suffice).
* Commuting-minimal-action route (symbolic dynamics transplant).
  `xl-commuting-minimal-action-gives-classifiable-witness`: if a compact
  metrizable finite-dimensional amenable `G`-space `X` carries a commuting free
  minimal action of `Z` (or of a locally finite group) `Gamma`, then `G` acts
  amenably on the unital stably finite classifiable algebra `C(X) x Gamma`
  (Følner-averaging the Reiter witnesses over `Gamma` gives the quasi-central
  approximation property).  So XL for `G` reduces to the dynamical statement
  (CMA_G).  `xl-commuting-minimal-action-forbids-proximal-factors`: any such
  `X` has no nontrivial proximal `G`-factor, so shift, Toeplitz and skew-product
  models built over boundaries (hyperbolic boundaries, tree ends, `G/P`) all
  die at the minimality step.  The surviving models must be amenable `G`-spaces
  without proximal factors.
* Invariant-AF-relation generalization and its obstruction
  (`xl-invariant-af-relation-gives-amenable-af-witness`).  If an amenable Cantor
  `G`-space carries a minimal AF relation `R = union R_n` with every compact open
  `R_n` preserved by `G` (classes may be permuted), then `G` acts amenably on the
  simple AF algebra `C*(R)`: class-averaged Reiter witnesses are exactly central
  in `C*(R_n)` and need no Følner averaging.  But such `X` admits no continuous
  `G`-map into `P(B)` for any nontrivial boundary `B` (minimal subsets of
  `P(B)^2` sit on the Dirac diagonal, and the `R`-saturation of a `G`-minimal set
  is dense).  Both routes therefore need an amenable `G`-space that does not
  map equivariantly into the measures of any boundary; whether such spaces
  exist (e.g. for free or hyperbolic groups) is the decisive open question.
* Groupoid equivalence behind both routes
  (`xl-groupoid-action-amenable-iff-semidirect-amenable`).  If `G` acts
  by automorphisms on an amenable étale groupoid `H`, the induced action on
  `C*_r(H)` is amenable iff `H x| G` is amenable (push Reiter functions along the
  cocycle `H x| G -> G`; nuclearity for the converse).  So XL for `G`, restricted
  to witnesses with a `G`-invariant untwisted Cartan subalgebra, is exactly the
  groupoid statement (GSA_G)
  (`xl-exact-groups-admit-amenable-semidirect-groupoid-models`).  The commuting
  and invariant-AF models are the cases where `G` commutes with `H` or preserves a
  compact open exhaustion, which is precisely what the boundary kills use; for
  automorphism actions that normalize `H` without such rigidity (for example
  `Gamma x| G` acting on `X` with `Gamma` amenable and minimal) only
  `H`-invariant boundary maps are excluded.
