---
rg: 2
id: sp4-projective-models-with-cocycles-to-one-round-strictly
kind: claim
title: Every exact finite-dimensional projective model of Sp_4(Z) whose cocycles tend to 1 rounds strictly in operator norm
distinct_from:
  rf-kazhdan-group-not-flexibly-hs-stable: that uses exact projective models with cocycles tending to 1 (Heisenberg covers of Z^2g x| Sp_2g(Z)) to refute flexible HS-stability of the affine symplectic group; this shows the same mechanism has no input at Sp_4(Z) itself.
  sp2g-z-flexibly-hs-stable: that is the open flexible stability claim; this only removes the scalar-cocycle family of candidate counterexamples at g = 2.
  isw-theorem-a-has-no-data-on-sp4-lattice: that removes the input of Ioana--Spaas--Wiersma Theorem A (a non-coboundary restriction to a subgroup); this is the rounding statement for the whole group, with no subgroup condition.
---

**ESTABLISHED (unreviewed).** Let `Γ = Sp_4(Z)` and let `α_n : Γ -> U(d_n)` be exact
projective unitary representations,

```text
α_n(g) α_n(h) = c_n(g,h) α_n(gh),     c_n ∈ Z^2(Γ;T),     c_n(g,h) -> 1 for all g,h.
```

Then for all large `n`, `α_n = β_n π_n` with `π_n : Γ -> U(d_n)` genuine representations and
`β_n : Γ -> T` scalars tending to `1` pointwise. So `||α_n(g) - π_n(g)||_op -> 0` for every
`g`.

Derivation: `sp4-projective-models-cocycles-to-one-round-strictly-proof`.

**What it rules out for `sp2g-z-flexibly-hs-stable` at `g = 2`.**
- **The Ioana--Spaas--Wiersma / Heisenberg witness has no analogue at `Sp_4(Z)`.** Such
  witnesses are exact finite-dimensional projective models with cocycles tending to 1, as in
  `rf-kazhdan-group-not-flexibly-hs-stable`. At `Sp_4(Z)` every one rounds strictly. Here
  `H_2(Sp_4(Z);Z)` has rank one (the Deligne--Maslov circle), but only finitely many of those
  classes are realized in finite dimensions (`sp4-fd-projective-multiplier-is-finite`).
- **What a counterexample must be.** A non-roundable asymptotic representation of `Sp_4(Z)`,
  if one exists, has genuinely non-scalar defects, or is only asymptotically projective. The
  second kind comes from twisted factors at non-realized twists, and a Connes-embeddable
  sequence of those is exactly what `sp2g-flexible-stability-forces-twisted-non-ce` says would
  refute the claim.
