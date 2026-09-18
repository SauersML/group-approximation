---
rg: 2
id: decidable-inputs-have-fp-houghton-like-shift-envelopes
kind: claim
title: Every infinite finitely presented group with solvable word problem has an enumeration nu and some n >= 2 with the Houghton-like envelope H_n(E_nu(P)) finitely presented
distinct_from:
  infinite-shift-higman-compiler: that asks for E_nu(P) = H_1(E_nu(P)) itself to be finitely presented, which forces the two-sided window ker(eta) finitely generated; this allows any n >= 2, where the germ-level condition is only that R_nu is finitely presented.
  decidable-inputs-admit-two-sided-fg-near-index-kernel: that is the germ gate of the n = 1 envelope; the germ gate here is strictly weaker and is met by generic enumerations.
  perfect-decidable-inputs-have-fp-shell-envelopes: that asks for a finitely presented Cantor shell envelope, whose germ gate needs a one-sided window; this is a permutation envelope on n rays.
---

**OPEN.**

**Statement.** Let `P` be an infinite finitely presented group with solvable word problem. Then there are a
bijection `nu : P -> N` and some `n >= 2` such that the Mallery--Zaremsky Houghton-like group `H_n(E_nu(P))` is
finitely presented.

It is enough for Boone--Higman: `boone-higman-via-houghton-like-shift-envelopes`.

**What is known.**
- **Germ level.** By `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`, for
  `n >= 2` the germ group `H_n(E_nu(P))/FSym` is finitely presented iff `R_nu` is. Free-shift enumerations give
  `R_nu ≅ P * Z`, so they pass the germ gate for every infinite finitely presented `P`.
- **But free-shift enumerations fail (bh-map, same day).** By `free-shift-houghton-like-envelopes-are-not-fp`,
  `H_n(E_nu(P))` is not finitely presented for any `n` when `P * <s> -> R_nu` is injective. So a witness `nu`
  must carry near relations. Item 3 there gives a sharper necessary condition: finitely many relations of
  `H_n(E_nu(P))` must determine `nu` up to right translation.
- **Necessary.** `R_nu` is finitely presented (`houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group` item 4). So every enumeration with a
  non-finitely-presented near shift group is excluded. That includes the square spiral enumeration of `Z^2`
  (`square-spiral-z2-near-shift-group-is-not-finitely-presented`), which fails here as it fails every other
  permutation or shell route.
- **Remaining gap.** Find an enumeration with finitely presented `R_nu` whose near relations make
  `H_n(E_nu(P))` finitely presented. The generic-enumeration route
  `decidable-houghton-envelopes-via-generic-nu-and-lifting` is dead: its lifting requirement is refuted.
- **Calibration, `P = Z`.**
  - The zigzag enumeration makes `E_nu(Z) = H_1(E_nu(Z))` finitely presented, as an index-12 subgroup of `E_4`
    (`zigzag-cyclic-shift-envelope-is-finitely-presented`).
  - The source remarks after Question 5.13 that `H_n(E_k)` contains `H_n(H_k) ≅ H_(nk)` with finite index. So
    `H_n(E_4)` is finitely presented for every `n >= 1`.
  - Whether `H_n(E_nu(Z))` itself is finitely presented for `n >= 2` is not recorded.

**How this can fail.** It is a statement about all pairs `(nu, n)`. A refutation needs an invariant of `P` that
defeats every enumeration and every `n >= 2`. By the germ theorem, such an invariant can no longer live on the
germ group for generic enumerations. It would have to see the finitary part `FSym`. The free-shift kill
(`free-shift-houghton-like-envelopes-are-not-fp`) does exactly this, through the conjugation action of `rho` on
transpositions.

## Attempts

- **Lifting criterion and its two natural bases (bh-free-47, 2026-09-18).**
  - *The criterion.* `fsym-extensions-lift-fp-via-pair-transitive-stable-subgroups` replaces the refuted lifting
    claim with a sufficient condition. Take a finitely presented base `K ⊇ FSym(X)` and letters `y_i`. Each `y_i`
    must conjugate into `<K, y_<i>` some finitely generated subgroup with finitely many orbits on pairs. Given a
    finitely presented `R_nu` (`n >= 2`), a witness reduces to such a certificate.
  - *Strand-map base.* It dies. `strand-map-bases-lift-only-bounded-displacement-letters` shows that over
    `H_n(E_2)`, or any base of eventual strand maps, a `rho_g` with `g` of infinite order is certified only if
    `[P : <g>] < ∞`. So only virtually cyclic inputs are reached.
  - *Lampshuffler base.* It also dies, for one-ended `P`. The base is `FSym(X)` together with the regular copies
    on all strands. `lampshuffler-bases-lift-no-shift-for-one-ended-inputs` shows every certified letter has near
    index zero, so no certificate exists.
  - *What survives.* A witness through the criterion needs one of: iterated certificates whose `C_i` use
    earlier letters outside both bases (for example window conjugates `s^-j lambda_g s^j`), a third kind of base,
    or an input with more than one end.
