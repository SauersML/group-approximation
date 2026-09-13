---
rg: 2
id: circle-rotation-zd-codings-are-not-of-finite-type
kind: claim
title: A free Z^d-action on the circle by rotations, coded by finitely many half-open arcs, is a free subshift that is not of finite type
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: that shows SFTs without finite orbits carry no residually finite action; this shows a class of free minimal subshifts is not of finite type, by rational perturbation of the rotation
  minimal-aperiodic-wang-shift-exists: that is Labbé's minimal aperiodic Z^2 SFT, a coding of a rotation of the 2-torus; this is about codings of rotations of the circle, which are never of finite type
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part3.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `1, θ_1, ..., θ_d` are linearly independent over `Q`, and `Z^d` acts on `R/Z` by
  `z -> z + m·θ`.
- `f` is a non-constant right-continuous coding by finitely many half-open arcs.
- `X` is the closure of the configurations `n -> f(z + n·θ)` in `A^(Z^d)`.

**Statement.** `Z^d` acts freely on `X`, and `X` is not a subshift of finite type.

**Mechanism.**
- The `B(r)`-patterns of `X` depend only on the cyclic order, with coincidences, of
  the finitely many points `e − k·θ`.
- Moving the endpoints inside their `Z^d·θ`-classes along with a nearby rational `θ'`
  preserves that order. So the rational coding is a periodic configuration all of whose
  `B(r)`-windows are legal.
- `X` has no periodic point, so that configuration lies outside `X`, for every `r`.

**Contrast.** Labbé's `Omega_U` codes a rotation of the 2-torus and is of finite type.
Arrangements of lines in the torus can be rigid, while points on the circle carry only a
cyclic order.

**Proof:** `circle-rotation-zd-codings-are-not-of-finite-type-proof`.
