---
rg: 2
id: twin-models-have-macroscopic-noncoincident-stabilizers
kind: claim
title: The two modular vertex stabilizers of a finite twin model differ on a fixed fraction of points, so expander-type twin deep models fail
distinct_from:
  expanding-matchings-need-a-shared-stabilizer: that is Lemma G, which charges only non-coincident expanding diagonal orbits and leaves coincident points free; this bounds the coincident fraction itself, for every finite set with the two vertex actions, and closes that loophole.
  twin-deep-vertex-models-give-homogeneous-microstates: that excludes exact twin models through the normal subgroup theorem; this gives a quantitative non-coincidence bound from Selberg property (tau) and tree geometry, which reproves the exact exclusion.
---

**ESTABLISHED (unreviewed).** `A = PSL_2(Z[1/2])`, `C_0 = PSL_2(Z)`, `C_1 = gC_0g^(-1)`,
`g = diag(1,2)`, with finite generating sets `S_0`, `S_1`.

1. **Spectral gap.** There is `λ_A > 0` with `max_(s∈S_0∪S_1) ||sf − f|| >= λ_A||f||` for all
   `f ∈ ℓ^2(A/C_0)`. It is `λ_A = 1/(4c_0 + 3c_1)`, where `c_i = |S_i|^(1/2)/κ_i` and `κ_i` is the
   Selberg `(τ)` constant.
2. **Non-coincidence.** If a finite set `W` carries actions of `C_0` and `C_1`, then at most
   `(1 − λ_A^2/4)|W|` points `w` satisfy `Stab_(C_0)(w) = Stab_(C_1)(w)`.
3. **Twin deep models.** Every `(TD_(R,ε))` with generating set `S_Δ` of `Δ_R` has, for each `h > 0`,
   at least `(λ_A^2/4 − 2ε − |S_Δ|ε/h)|W|` points that are deep on both sides, non-coincident,
   and in a diagonal `Δ_R`-orbit of `(w,w)` with Cheeger constant below `h`.

**Readings.** With `ε = 0`, item 2 reproves that exact twin deep models do not exist, without the normal
subgroup theorem. Any family whose diagonal `Δ_R`-orbits have a uniform Cheeger constant `h` has
`ε >= λ_A^2 h/(4(2h + |S_Δ|))`. So random-lift and other expander ansätze are dead whether or not
their stabilizers coincide. A successful family must put a fixed fraction of its mass on
non-coincident, non-expanding diagonal orbits while staying asymptotically free.

Proof in `twin-models-have-macroscopic-noncoincident-stabilizers-proof`.
