---
rg: 2
id: stw99-problem-xxxiv-dynamical-characterisation
kind: claim
title: Z-stability of minimal amenable crossed products is dynamically characterised by almost finiteness (STW Problem XXXIV)
root: true
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

**Problem XXXIV of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(their Challenge): characterise dynamically when `C(X) ⋊ G` is
`Z`-stable, for free minimal actions of countable discrete amenable
groups.  Closed-form candidate recorded here (the optimistic reading
STW name): `C(X) ⋊ G` is `Z`-stable iff the action is almost finite
iff it has mean dimension zero / the small boundary property — open
already for `G = Z`.

## Attempts

* One direction is Kerr's theorem (almost finite ⟹ `Z`-stable).  The
  KLTV / Elliott--Niu C*-description makes the converse a precise
  relative-vs-absolute regularity question: SBP ⟺ relative uniform Γ
  of `(C(X) ⊆ C(X)⋊G)` and almost finiteness ⟺ relative tracial
  `Z`-stability, so the candidate characterisation says ABSOLUTE
  `Z`-stability of the crossed product forces the RELATIVE property of
  the inclusion.  The Giol--Kerr example is consistent (both fail);
  a counterexample would be a minimal action whose crossed product is
  `Z`-stable while the canonical Cartan inclusion fails relative Γ —
  i.e. regularity created by the algebra away from the diagonal.  No
  mechanism producing central sequences that avoid every Cartan
  conditional expectation is known; conversely proving none exists is
  a Cartan-rigidity statement for Γ, untouched in the literature.
