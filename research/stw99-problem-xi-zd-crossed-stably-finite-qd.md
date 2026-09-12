---
rg: 2
id: stw99-problem-xi-zd-crossed-stably-finite-qd
kind: claim
title: Stably finite crossed products of Z^d-actions on compact spaces are quasidiagonal and AF-embeddable (STW Problem XI)
root: true
distinct_from:
  stw99-problem-vii-blackadar-kirchberg: that is the general nuclear stably-finite quasidiagonality problem; this is its dynamical test case for C(X) x| Z^d, where Pimsner's theorem settles d = 1 and the traceless and faithful-trace regimes are settled by Gabe and Tikuisis--White--Winter respectively, isolating a dynamical extension problem.
  stw99-lxxxvi-berend-groups-decomposition-rank: that concerns decomposition rank of specific Z^2-actions on T^3; this concerns quasidiagonality of stably finite Z^d-crossed products in general, and the Berend systems are covered here by the faithful Haar trace.
artifacts:
  - research/artifacts/stw99-xi-xii-dynamics-qd-2026-08-30.md
  - research/artifacts/stw99-xi-clopen-support-gluing-2026-08-30.md
  - research/artifacts/stw11-transfinite-clopen-filtration-audit-2026-08-30.md
  - research/artifacts/stw11-lattice-coupled-cyclic-products-audit-2026-08-30.md
  - research/artifacts/stw11-folner-capacity-audit-2026-08-30.md
  - research/artifacts/stw11-bell-circle-actions-primary-source-2026-08-30.md
---

**Problem XI of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Let
`X` be compact metrisable, `d ≥ 2`, and `Z^d ↷ X`.  If `C(X) ⋊ Z^d` is
stably finite, must it be quasidiagonal?  AF-embeddable?  STW add that it
is not even known when such crossed products are stably finite.

For `d = 1` everything is Pimsner's theorem: AF-embeddable ⟺
quasidiagonal ⟺ stably finite ⟺ no open `U` with `α(U) ⊊ U`.

## Attempts

* **Necessary condition for stable finiteness, any `d`.**  If some
  `g ∈ Z^d` compresses an open set (`gU ⊊ U`), Pimsner's
  construction produces an infinite projection in the subalgebra
  `C(X) ⋊ ⟨g⟩`, which stays infinite in `C(X) ⋊ Z^d`.  So elementwise
  incompressibility is necessary; the open question is whether joint
  (staircase) compressions can occur without elementwise ones, i.e.
  whether an isometry-like element `Σ_i f_i u_{g_i}` can scale without a
  single-generator witness.  On zero-dimensional `X` this is the
  type-semigroup paradoxicality theory (Rainone; Rainone--Sims;
  Bönicke--Ma dichotomies), where stable finiteness is characterised by
  states/f.a. invariant measures on the type semigroup.
* **The two solved regimes.**  (i) If `X` carries a faithful invariant
  probability measure, the crossed product has a faithful amenable trace
  and is nuclear with the UCT (Tu), so the
  Tikuisis--White--Winter/Gabe/Schafhauser AF-embedding theorem answers
  everything.  (ii) If the crossed product is traceless (no nonzero lsc
  tracial weight), Gabe's GAFA theorem gives stably finite ⟺
  quasidiagonal ⟺ AF-embeddable outright, with the primitive-ideal
  criterion.
* **Free abelian circle actions are quasidiagonal, including the non-minimal
  extension case.**  Bell, arXiv:2604.18410v2, Theorem 3.14 (Theorem A(iii)),
  proves that `C(T) rtimes G` is quasidiagonal for every free action of a
  countably infinite discrete abelian group `G`.  For `G=Z^d`, `d>=2`, this
  gives an exact positive subclass of XI beyond the global-faithful-trace
  regime: in the non-minimal case the unique invariant measure is supported
  on the proper minimal set, while Bell crosses the extension with ideal a
  direct sum of stabilized `C_0(R)` algebras.  The imported claim is
  `bell-free-abelian-circle-crossed-products-are-qd`.  Bell's Remark 3.15
  explicitly leaves AF embeddability unverified for the non-minimal case, so
  neither that conclusion nor arbitrary compact coefficient spaces are
  promoted here.
* **An exact orbit-capacity test for the faithful regime.**
  `stw11-folner-capacity-faithful-trace-criterion` shows that a faithful
  invariant probability exists exactly when every nonzero positive
  continuous function has positive maximal average along the standard
  Følner boxes.  Each positive limit yields an invariant empirical-orbit
  limit detecting that function; a countable convex mixture is faithful.
  Consequently the crossed product embeds into a unital simple AF algebra.
  In particular this solves XI for every action with dense minimal points,
  including actions with infinitely many accumulating minimal subsystems and
  no compact-open support filtration or product-of-cyclic presentation.
* **Structural reduction (this lane).**  Tracial weights on
  `C(X) ⋊ Z^d` restrict to invariant Radon measures on open invariant
  pieces of `X`.  Filtering `X` by the closure of supports of invariant
  measures decomposes the crossed product into a (possibly transfinite)
  filtration whose subquotients are either traceless dynamical algebras
  (Gabe regime) or algebras of pieces carrying faithful-support invariant
  measures (TWW regime, after passing to the measured supports).  Both
  kinds of pieces are individually AF-embeddable when stably finite; the
  entire content of Problem XI is therefore the permanence of
  quasidiagonality/AF-embeddability along these specific dynamical
  extensions — quasidiagonality is not closed under extensions in
  general, and Brown's AF ⋊ Z work (the model for Problem XII) is
  exactly the `d = 1` template for handling such glueing via
  incompressibility.
* **Compact-open support extensions are quasidiagonal.**
  `stw11-clopen-exhaustion-glues-qd` closes the quasidiagonality part of the
  extension reduction whenever each open invariant stratum has an
  increasing exhaustion by compact-open invariant subsets.  Their
  characteristic functions are central projections in the crossed product
  and form an approximate unit for the stratum ideal, so quasidiagonality of
  the compact corners and terminal closed-support quotient glues through
  any finite such filtration.  In particular, this proves quasidiagonality
  when the whole algebra is stably finite, the open-stratum ideal is
  traceless, and the closed subsystem carries a full-support invariant
  probability measure.  The induced quotient trace kills the open ideal,
  so this mixed case is not covered by the global faithful-trace theorem.
  This does not by itself give an AF embedding; that upgrade would import
  Problem VIII.
* **Transfinite cumulative support filtrations are quasidiagonal.**
  `stw11-transfinite-cumulative-clopen-filtrations-glue-qd` replaces the
  finite backward induction by a transfinite forward construction.  For a
  continuous ordinal-indexed decreasing chain of invariant closed supports, it
  is enough that every cumulative open complement have an invariant
  compact-open exhaustion, every successor-stratum crossed product be
  quasidiagonal, and the terminal crossed product be quasidiagonal.  The
  cumulative ideals are quasidiagonal by successor two-cut gluing and
  norm-local limit gluing; one final projectional cut recovers the ambient
  algebra.  Separate compact-open exhaustions of the relative strata are
  not enough: their characteristic functions need not be ambient
  projections.
* **Lattice-coupled products of cyclic systems are AF-embeddable.**
  `stw11-lattice-coupled-cyclic-products-are-af-embeddable` gives the full
  stably finite `iff` quasidiagonal `iff` AF-embeddable conclusion for every
  action on `product_i X_i` of the form

  ```text
  g.(x_i)_i=(alpha_i^(L(g)_i)(x_i))_i,
  ```

  where `L:Z^d->Z^m` is any integer lattice map and the `alpha_i` are
  arbitrary homeomorphisms.  Stable finiteness detects a crossed product by a
  nonzero power of every active `alpha_i` inside the higher-rank algebra.
  Pimsner's compression criterion returns from that power to `alpha_i`, and
  the lattice crossed product embeds in the tensor product of the resulting
  cyclic AF hosts, the inactive commutative coefficients, and the torus from
  `ker L`.  This includes skew rank-two actions whose generators each move
  several factors, assumes neither a faithful trace nor a clopen filtration,
  and gives the stronger AF-embedding conclusion.
