---
rg: 2
id: char-zero-linear-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated linear group over a field of characteristic zero satisfies Boone--Higman
root: true
distinct_from:
  char-two-linear-groups-satisfy-boone-higman: that is the characteristic-two class, reached through Leavitt tensor hosts over finite fields; this is the characteristic-zero class, where the corresponding Leavitt unit groups have congruence kernels.
  algebraic-linear-groups-satisfy-boone-higman: that is the established transcendence-degree-zero part; this is every transcendence degree.
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's rational case; this is the full characteristic-zero linear class.
  positive-char-surface-linear-groups-satisfy-boone-higman: that is a positive-characteristic class; this is characteristic zero.
---

**OPEN.** Let `K` be a field of characteristic zero and let `H <= GL_n(K)` be
finitely generated. Then `H` embeds in a finitely presented simple group.

*Marked `root` because it is a natural class question in its own right.* Such
`H` are residually finite and have solvable word problem, so this is a case of
the Boone--Higman conjecture.

**Established part.** Transcendence degree zero is
`algebraic-linear-groups-satisfy-boone-higman`, which follows from Zaremsky's
`GL_n(Q)` theorem by restriction of scalars.

**Open part.** Exactly the finitely generated linear groups whose matrix entries
generate a field of positive transcendence degree over `Q`. The first cases are
`SL_3(Z[t])` and the finitely generated subgroups of `GL_n(Q(t))`.

## Attempts

1. **Leavitt unit groups over characteristic-zero rings.** The positive-characteristic
   hosts of `positive-char-surface-linear-groups-satisfy-boone-higman` put
   polynomial rings inside Leavitt tensor algebras over finite fields.
   *Dies:*
   - over a finitely generated characteristic-zero domain, the unit group has
     congruence kernels, so it is not simple
     (`char-zero-leavitt-unit-groups-have-congruence-kernels`);
   - over a characteristic-zero field, the scalars are central, and Khanh's
     acyclicity and Steinberg comparison use scalar actions of finite fields,
     which that field does not contain.

   *Closed in general (2026-09-12):* `char-zero-algebra-unit-hosts-exclude-unipotents`.
   No finitely generated simple subgroup of `A^x / C`, with `C` central, contains a
   central unit times a non-central unipotent, whenever the lifts live in a subring
   in which no non-zero element is divisible by infinitely many primes. This covers
   algebras with free integral forms, and matrices over finitely generated fields.
   So any host that contains the input through matrices over an algebra already
   fails for `SL_3(Z)`, whatever the transcendence degree.
2. **Affine self-similar groups, extending Zaremsky's rational route.** His
   Example 4.7 needs a coordinate ring `R` with a finite-index principal ideal
   `xR` and `∩ x^k R = 0`.
   *Dies for commutative coordinates:* no finitely generated commutative domain
   of positive transcendence degree has such an `x`, and the `p`-adic digit
   version (`t` sent to a transcendental `p`-adic integer) is not section-closed
   (`affine-self-similar-coordinate-rings-are-one-dimensional`).
   *Not excluded:* noncommutative coordinate rings, and self-similar hosts that
   are not affine.
3. **Twisted Brin--Thompson hosts.** Zaremsky's action criterion needs a finitely
   presented overgroup whose action has finitely generated point stabilizers and
   finitely many orbits of pairs.
   *Not attempted here;* the lane `bh-twisted-brin-thompson` owns that route.
4. **Hosts ruled out by property (T)** (lane `bh-char-zero-transcendental`,
   2026-09-12; literature imported, not re-verified from source).
   `SL_3(Z[t]) = E_3(Z[t])` (Suslin), and `EL_3` of every finitely generated ring
   has (T) (Ershov--Jaikin-Zapirain 2010). So the input has (T) and (FA).
   *Dies:*
   - a-T-menable hosts such as `V` (Farley), which contain no infinite (T) group;
   - lattices in products of locally finite trees, such as Burger--Mozes groups;
   - graph-of-groups towers, which only return a base piece
     (`fa-subgroups-of-graph-towers-lie-in-base-pieces`).
5. **What survives:** homeomorphism hosts.
   - **Target shape.** A finitely presented full Cantor group containing standard
     `V` and `SL_3(Z[t])` would suffice for that case
     (`fp-full-binary-cantor-groups-have-type-a-actions`).
   - **Candidate Cantor action.** `SL_3(Z[t^(+-1)])` acts faithfully on
     `(Z_p^3)^Z` through Laurent-polynomial matrices. Each element acts as a
     cellular automaton in the `Z` direction and as a finite-state transducer in
     the `p`-adic direction.
   - **Open:** whether a full group of this Brin--Thompson type with infinitely
     many directions is finitely presented. See
     `research/artifacts/bh-char-zero-transcendental-2026-09-12.md`.
