---
rg: 2
id: brin-thompson-2v-is-not-a-t-menable
kind: claim
title: "The Brin-Thompson group 2V does not have the Haagerup property"
distinct_from:
  brin-thompson-groups-nv-are-a-t-menable: that claim is the affirmative answer for every nV; this is its negation for 2V, which by 2V <= nV denies the Haagerup property for every n >= 2
---

The Brin–Thompson group `2V` admits no proper conditionally negative definite
function. Because `2V <= nV` for every `n >= 2` (via `g ↦ g x id`), this
denies the Haagerup property for all `nV`, `n >= 2`, and answers the Haagerup
part of Zaremsky Problem 2.7 negatively.

## Attempts

- **Relative (T) inside 2V.** It would suffice to find an infinite subset of
  `2V` with relative property (T), e.g. a copy of `Z^2 ⋊ Γ` with `Γ` a
  non-amenable subgroup of `SL_2(Z)` acting linearly, where `(Z^2 ⋊ Γ, Z^2)`
  has relative (T) (Burger). Brick-canonical maps have no shears, so such a
  copy cannot be "geometric". An abstract embedding would also bear on
  Problem 2.19 (GL_n(Z) in mV), owned by z2-19-glnz-q-2v.
- **Infinite Kazhdan subgroups.** An infinite (T) subgroup of `2V` would do.
  This is exactly the open side of Problem 2.19 for `2V`.
- Both are untested.
- 2026-09-18 (swarm-0917-w12-w12-nv-pull): the relative-(T) route, decomposed and partly killed.
  - *Reduction.* Suppose some `Z^2 ≤ nV` has non-amenable normalizer image `Γ ≤ GL_2(Z)`. Lift
    free generators of `Γ` to get `⟨Z^2, Φ, Ψ⟩`, a quotient of `Z^2 ⋊ F_2` whose kernel `K`
    meets `Z^2` trivially. Then `[K, Z^2] ≤ K ∩ Z^2 = 1`, and `F_2` acts faithfully, so `K = 1`.
    So `Z^2 ⋊ F_2 ≤ nV`, and Burger's relative (T) for `(Z^2 ⋊ Γ', Z^2)` would refute
    Haagerup. The Burger theorem is cited from memory, not verbatim.
  - *Decomposition via the compiler.* Build codes over a common `Z^2`:
    - P1: an `mI` code;
    - P2: an `mA` code with `A` hyperbolic, which gives a Sol lattice in `(k+1)V`;
    - P3: an `mB` code with `⟨A, B⟩` free, which gives the Burger pair.
  - *Kill.* `coordinate-shadows-rigidify-abelian-normalizers-in-nv` (ESTABLISHED) shows that over
    any block-split `Z^2`, including every SMART-odometer product, all twisting matrices are
    diagonal. So P2 dies there. More generally, the route dies whenever some coordinate-shadow
    set `D_J` is finite and nonempty.
  - *Survivors.* A survivor must be a coordinate-mixing `Z^2`, with every `D_J` empty or
    infinite. No such `Z^2` with a hyperbolic normalizer element is known. Finding one, or
    proving that none exists, is the open step.
- 2026-09-19 (swarm-0917-w17-w17-nv-break): tried to realize Burger pairs through their natural completion models, including in characteristic p. This class of models is dead.
  - *Candidate.* In characteristic p, `(EL_2(F_2[t]) ⋉ F_2[t]^2, F_2[t]^2)` has relative (T) by `elementary-linear-semidir-pair-relative-t`. Its base is locally finite, so it evades the sibling obstruction that normal relative-(T) bases in `W(Z)` or `[[X]]` are locally finite. It also evades the Z^2 coordinate-shadow kill.
  - *Failure in coordinates.* Translations act on `F_2[[t]]^2 = C^2` by prefix changes, so they lie in 2V. The shear `e_12(t)` is a carry-free linear cellular automaton, not a brick map. The same happens for `Z^2 ⋊ SL_2(Z)` on `Z_2^2`.
  - *Kill.* `nv-orbit-relations-are-hyperfinite` (ESTABLISHED) shows every subgroup of `nV` has hyperfinite measured orbit relation on `C^n`. So no essentially free probability-preserving action of a non-amenable group is Borel-conjugate into `nV`. All these completion models are free and Haar-preserving, so they die for every identification of the Cantor set, not only the standard one.
  - *Survivors.* An embedding of a Burger pair must have non-amenable stabilizers on a positive-measure set for every invariant probability measure, or have no invariant probability measure at all. The open step is a construction of that kind, for example one built from supports or germs rather than from a completion.
- 2026-09-20 (swarm-0917-w22-w22-z-follow): the char-p lamp route, made explicit and cut down to its dynamical core.
  - *Route.* New route `brin-thompson-2v-not-a-t-menable-via-char-p-lamp-lifts`. It uses the ESTABLISHED criterion `char-p-burger-lamp-realizations-refute-haagerup` together with the new OPEN hole `brin-thompson-2v-lifts-el2-laurent-linear-ca-generators`. That hole asks for 2V lifts of the generators of `EL_2(F_p[t,t^-1])` acting on `(F_p^2)^Z`, all through one `φ`. It is the only missing input.
  - *Kill.* `piecewise-baker-torus-lifts-force-monomial-lamp-linear-parts` (ESTABLISHED) covers every realization in which some lift of `h` has a power that is nV-conjugate to a piecewise local baker map. For every such realization, all lifted linear parts are monomial, so no shear lifts and the route fails.
  - *Sharpness.* A two-box baker lifts both `h` and `w`.
  - *Survivors.* Lifts of `h` that are not piecewise baker, and the one-sided `F_p[t]` variant with countably many lifts.
