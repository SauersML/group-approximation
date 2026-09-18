---
rg: 2
id: one-fp-simple-group-contains-every-integral-linear-group
kind: claim
title: One finitely presented simple group contains every finitely generated subgroup of every GL_n(Z)
distinct_from:
  finitely-generated-linear-groups-satisfy-boone-higman: that gives each finitely generated linear group its own finitely presented simple host; this asks for one host for the whole integral linear class at once.
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that is an unconditional common host for the groups in some nV; this is the integral linear class, which includes SL_3(Z), H_3(Z) and every polycyclic group.
  all-hyperbolic-groups-lie-in-one-fp-simple-group: that is the hyperbolic class; this is the integral linear class.
---

**OPEN.** There is a finitely presented simple group containing a copy of `GL_n(Z)`
for every `n` (equivalently, of every finitely generated subgroup of every `GL_n(Z)`).
It would contain at once every polycyclic group, every finitely generated nilpotent
group, every finite group, every arithmetic subgroup of every `GL_n(O_K)`, and every
finitely generated virtually special group.

- **Known part.** The virtually special groups already lie in the
  single host of `one-fp-simple-group-contains-every-brin-thompson-subgroup`. Each
  individual `GL_n(Z)` is Boone–Higman (`finitely-generated-linear-groups-satisfy-boone-higman`).
- **Sufficient conditions.**
  1. Boone–Higman for the explicit three-generated group `Σ = E(Z) ⋊ Z` of
     `elementary-shift-group-contains-every-integral-linear-group`: route
     `integral-linear-one-host-via-elementary-shift-group`.
  2. Zaremsky Problem 2.19(c), `every-gl-n-z-embeds-in-some-brin-thompson-group`: then
     every `GL_n(Z)` lies in `U = DV_F`: route `every-integral-linear-group-in-one-host-via-nv`.
  3. Boone–Higman for the explicit finitely presented group `E(Z; D) ⋊ F`
     (`finitary-steinberg-extensions-by-oligomorphic-actions-are-fp`): route
     `integral-linear-one-host-via-fp-elementary-thompson-group`.
  4. Finite presentation of the derived subgroup of the twisted integral-affine full
     group (`twisted-integral-affine-full-group-is-finitely-presented`): route
     `integral-linear-one-host-via-twisted-integral-affine-full-group`.
  5. Boone–Higman itself, via `common-decidable-hosts-iff-uniform-word-problem`: the
     standard finite presentations of the `GL_n(Z)` form a c.e. class with uniformly
     solvable word problem (matrix multiplication).
- **Why neither known method applies.** `Σ` is not linear and not residually finite, so
  Zaremsky's self-similar affine hosts (one per `n`) do not combine; and `SL_3(Z)` is
  Kazhdan and contains `H_3(Z)`, so the known Brin–Thompson embeddings (virtually
  special groups, `Q`, `BS(1,3)`) do not reach it.
