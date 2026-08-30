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
---

**Problem XI of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Let
`X` be compact metrisable, `d ≥ 2`, and `Z^d ↷ X`.  If `C(X) ⋊ Z^d` is
stably finite, must it be quasidiagonal?  AF-embeddable?  STW add that it
is not even known when such crossed products are stably finite.

For `d = 1` everything is Pimsner's theorem: AF-embeddable ⟺
quasidiagonal ⟺ stably finite ⟺ no open `U` with `closure(α(U)) ⊊ U`.

## Attempts

* **Necessary condition for stable finiteness, any `d`.**  If some
  `g ∈ Z^d` compresses an open set (`closure(gU) ⊊ U`), Pimsner's
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
