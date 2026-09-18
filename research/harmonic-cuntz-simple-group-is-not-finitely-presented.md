---
rg: 2
id: harmonic-cuntz-simple-group-is-not-finitely-presented
kind: claim
title: The harmonic Cuntz simple group EL_3(C_h)/Q^x is not finitely presented
distinct_from:
  harmonic-cuntz-simple-group-is-finitely-presented: that is the OPEN assertion that the group is finitely presented; this is its negation, so that assertion is false.
  leavitt-scalar-commutators-block-fp-central-quotients: that is the general obstruction for groups whose commutator subgroup meets the centre in a non-finitely-generated subgroup; this is its instance for EL_3 of the harmonic Cuntz ring.
  leavitt-resolvent-derived-units-mod-centre-not-fp: that is the same obstruction for the derived unit group of the Leavitt resolvent ring R_L; this is the instance for the elementary group of C_h.
---

**ESTABLISHED** by `harmonic-cuntz-simple-group-is-not-finitely-presented-proof`
(lane proof, not independently reviewed; elementary, no novelty claimed).

**Statement.** Let `C_h` be the harmonic Cuntz ring of
`harmonic-cuntz-ring-is-purely-infinite-simple`, `H = EL_3(C_h)`, and
`Z = H ∩ {λI : λ ∈ Q^x}`. Then:
- `Λ_h = H/Z` is not finitely presented;
- more generally, `H/C` is not finitely presented for any `C` with
  `Z ≤ C ≤ Z(H)`. The same holds for `EL_N(C_h)` for every `N >= 3`.

So `harmonic-cuntz-simple-group-is-finitely-presented` is false. The route
`gl-n-q-via-harmonic-cuntz-host` does not reach `gl-n-q-embeds-in-fp-simple-group`,
and the route `rational-leavitt-fp-simple-via-harmonic-host` does not reach its target.

**Why.** `H` is perfect, and its central subgroup `Z = Q^x·I` is not finitely
generated. A finitely presented quotient `H/C` by a central subgroup would make
`C ∩ [H,H]` a quotient of the finitely generated group `H_2(H/C; Z)`.

**What survives.** As in `leavitt-scalar-commutators-block-fp-central-quotients`
(Consequences), a finitely presented simple group built from `C_h` must be a
subquotient `H'/M` with `M` not central, or with `H'` containing no full copy of
`L_Q(1,2)^x`. The group `Λ_h` stays a finitely generated simple group with
solvable word problem containing every `GL_n(Q)`
(`harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q`). It is only the finite
presentation that fails.
