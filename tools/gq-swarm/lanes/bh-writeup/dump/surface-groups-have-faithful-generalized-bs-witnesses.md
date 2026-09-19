---
rg: 2
id: surface-groups-have-faithful-generalized-bs-witnesses
kind: claim
title: For a closed hyperbolic surface group G, some nontrivial group in BS_G acts faithfully on its Bass–Serre tree, namely an S-arithmetic quaternion lattice
distinct_from:
  free-generalized-bs-groups-have-type-a-overgroups: that uses Burger–Mozes amalgams as the faithful witness for free groups; this supplies a faithful witness for surface groups, which are one-ended and not commensurable with free groups.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that imports the reduction "one faithful witness in BS_G suffices"; this is the witness for surface groups.
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

**ESTABLISHED** (lane proof, not reviewed; route
`surface-groups-have-faithful-generalized-bs-witnesses-proof`). No priority claimed.

Let `G = π_1(Σ)` for a closed surface `Σ` with `χ(Σ) < 0` (orientable or not), or more generally any
group abstractly commensurable with a cocompact Fuchsian group. Then the class `BS_G` of
Bux–Llosa Isenrich–Wu contains a nontrivial group that acts faithfully on its Bass–Serre tree.

**Witness.** Let `D` be the quaternion algebra over `Q` ramified exactly at `2` and `3` (so split at
`∞` and at `5`), `O` a maximal order, and `Λ = (O ⊗ Z[1/5])^1` its group of reduced norm `1`.
Then `Λ̄ = Λ/{±1}` acts on the `6`-regular Bruhat–Tits tree of `SL_2(Q_5)`:
- faithfully and without inversions;
- with finitely many orbits;
- with vertex stabilizers cocompact arithmetic Fuchsian groups (norm-one groups of maximal
  `Z`-orders of `D`, modulo `±1`);
- with edge stabilizers of index `6` in them.
So `Λ̄ ∈ BS_G` is the required witness.

Nothing here is specific to the discriminant: any division quaternion algebra over `Q` that is
split at `∞` and at some prime `p` works the same way, with a `(p+1)`-regular tree.
