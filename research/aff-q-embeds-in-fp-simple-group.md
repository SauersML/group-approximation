---
rg: 2
id: aff-q-embeds-in-fp-simple-group
kind: claim
title: The rational affine group Aff(Q) = Q x| Q^x embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the root for GL_n(Q), n >= 2; this is its stepping stone Aff(Q) = {[[a,b],[0,1]]} <= GL_2(Q), which the root implies and which is necessary for it.
  borel-two-q-is-units-times-aff-q: that proves B_2(Q) = Q^x x Aff(Q) and reduces B_2(Q) to Aff(Q) inside B_A; this is the open embedding question for Aff(Q) itself.
  rational-linear-groups-satisfy-boone-higman: that covers the finitely generated subgroups, which here all lie in some Aff(Z[1/m]); this is the whole countable group.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes two specific hosts, T-bar and Aut(F); this asks for some finitely presented simple host.
---

**OPEN.** There are a finitely presented simple group `S` and an injective
homomorphism `Aff(Q) -> S`, where `Aff(Q) = {x ↦ a x + b : a ∈ Q^x, b ∈ Q} ≅ Q ⋊ Q^x`.

**Status as a target.** This is a stepping stone of the swarm, not a printed question.
- `Aff(Q) <= B_2(Q) <= GL_2(Q)`, so `gl-n-q-embeds-in-fp-simple-group` implies this
  claim.
- Conversely, `B_2(Q) ≅ Q^x × Aff(Q)` (`borel-two-q-is-units-times-aff-q`), so a
  `B_A` host for `Aff(Q)` gives one for `B_2(Q)`.
- It is the smallest non-abelian rational stepping stone. It has the divisibility of
  `(Q,+)` and the dilations `BS(1,p) <= Aff(Q)` for every prime `p`, but none of the
  rigidity of `SL_3(Z)`.

## Known

- **Pieces.** `(Q,+)` and `Q^x` embed in `VA` (countable abelian). `(Q,+)` also embeds
  in `2V` (`rationals-embed-in-brin-thompson-group-2v`). Every finitely generated
  subgroup lies in some `Aff(Z[1/m]) <= GL_2(Q)`, so it embeds
  (`rational-linear-groups-satisfy-boone-higman`).
- **Detection.** A homomorphism from `Aff(Q)` is injective iff the translation `t_1`
  survives, iff the image is non-abelian
  (`gl-n-q-embeddings-detected-by-nontrivial-homomorphisms`, item 3). In `Aff(Q)`, all
  nontrivial translations are conjugate, and `t_b` is conjugate to `t_b^m` for every
  `m ≠ 0`.
- **Reduction.** `Aff(Q)` embeds in a finitely presented simple group as soon as it
  lies in a finitely presented group with a type (A) action
  (`type-a-action-gives-boone-higman-for-subgroups`). This covers countable inputs; see
  `permutational-host-forms-agree-for-countable-inputs`.

## What a host must have

- **H1, not residually finite.** It contains no residually finite group, because
  `(Q,+)` is divisible (root O1).
- **H2, exponential distortion.** It contains `BS(1,p)` for every prime `p`. This
  excludes `VA` and every subgroup of it: `V`, `T-bar`, Brin's `A` (root O4,
  Burillo–Felipe). For `T-bar` and `Aut(F)` there is also
  `aff-q-does-not-embed-in-aut-thompson-f`.
- **H3, no natural piecewise-linear action.** A finitely generated host whose
  generators have finitely many linear parts cannot act with the dilations fixing a
  point with derivative `a` (`fg-piecewise-linear-hosts-omit-natural-gl-n-q`).
- **H4, no easy closures.** Abelian-lamp permutational wreath products add nothing
  (`abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q`). Central lifts cannot supply the
  translation divisibility (`lifts-add-no-unipotent-divisibility`).
- **H5, Brin–Thompson hosts.** An `nV` host needs `BS(1,2) <= nV`
  (`rational-stepping-stones-in-nv-need-bs12-or-heisenberg`; OPEN as
  `bs12-embeds-in-brin-thompson-2v`). Its translation subgroup must also be an
  exponent-flat copy of `Q` (`nv-rational-subgroups-with-power-conjugacy-are-flat`). The
  landed copy of `Q` in `2V` is not one. A copy of `Q` with no periodic points at all
  exists in `3V` (`three-v-contains-aperiodic-rationals`).

## Attempts

1. **Natural piecewise-affine or projective actions (2026-09-17): dead.** Derivatives
   and coefficients stay in a finitely generated ring. See H3 and
   `germ-extensions-omit-standard-gl-n-q`.
2. **The Kojima–Sheng tower in `2V` as the translation group (2026-09-17, gq-affq):
   dead.** `s_0 = t × id` has a hyperbolic fixed point, so no element of that copy of
   `Q` is conjugate in any `nV` to a proper power
   (`nv-rational-subgroups-with-power-conjugacy-are-flat`, item 3).
3. **An aperiodic tower in `3V` (2026-09-17, gq-affq): alive, first step only.** The
   root tower `Q_T` over the SMART moving-tape element `T ∈ 2V` has no periodic points
   (`three-v-contains-aperiodic-rationals`). It passes the periodic-exponent tests.
   - *Next falsifiable step:* find `f ∈ nV` with `f s_0 f^-1 = s_0^2` for
     `s_0 = T × id`, or refute it with the `(log N)^2` exponent bound (item 4 of
     `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`) or the logarithmic
     table-length bound (`bs12-images-in-nv-have-logarithmic-table-length`). Both
     reduce to the head excursions of SMART.
   - *Beyond that:* commuting dilations for all primes, acting on all of `Q_T` at once.
4. **Röver–Nekrashevych hosts over rational Iwahori groups.** A live route of lane
   gq-rn-varying-degree, in drafts at the time of writing. `PGL_2(Q) ⊇ Aff(Q)` acts
   on `P^1(Q_p)` with local actions in the rational Iwahori group, which is not
   finitely generated. Divisibility by `p` then comes from level shifts, and
   divisibility by the other primes from the local translations. The route needs that
   local group, or the part used by `Aff(Q)`, inside a finitely presented
   self-similar group. Nothing about it is recorded here as established.
