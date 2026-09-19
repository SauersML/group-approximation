---
rg: 2
id: leavitt-central-units-lie-in-derived-normal-subgroups
kind: claim
title: In a ring with a binary Leavitt family every central unit lies in [P,P] for each normal subgroup P of the unit group containing V, so such P have no finitely presented perfect quotient by a central subgroup containing infinitely generated central units
distinct_from:
  q-coefficient-leavitt-tensor-unit-groups-are-fp: that obstruction needs P finitely presented and concludes only that P/Q^x is not finitely presented; this needs no finiteness of P and excludes every finitely presented perfect central quotient.
  leavitt-resolvent-derived-units-mod-centre-fp-simple: that is the specific target for the resolvent ring, refuted by the instance of this theorem recorded in leavitt-resolvent-derived-units-mod-centre-not-fp-simple.
  leavitt-unit-groups-over-every-field-are-simple-mod-scalars: that proves L_k(1,2)^x / k^x simple; this shows it, and every normal V-containing unit subgroup modulo the centre, is never a finitely presented perfect group when k is infinite.
  leavitt-units-embed-in-their-scalar-quotient: that embeds the unit group in its scalar quotient; this places the central units inside the second derived subgroup of every normal V-containing subgroup.
---

**ESTABLISHED** by `leavitt-central-units-derived-proof` (elementary; not independently
reviewed; no novelty claimed. The K_1 shadow of part 1 is the standard `[λ] = 2[λ]`
computation).

Let `R` be a nonzero unital ring with a binary Leavitt family
`s_1, s_2, t_1, t_2` (`t_i s_j = δ_ij`, `s_1 t_1 + s_2 t_2 = 1`). Let `U = R^x`, let
`V ≤ U` be the standard copy of Thompson's group (`Σ s_(β_i) t_(α_i)` over pairs of
complete prefix codes), and let `Z_R = Z(R) ∩ U` be the central units.

1. **Central units are double commutators.** For every normal subgroup `P ⊴ U` with
   `V ≤ P`, we have `Z_R ≤ [P, P]`. In particular `Z_R ≤ [[U,U],[U,U]]`.
2. **No finitely presented perfect central quotients.** Suppose `Z_R` is not finitely
   generated. Let `P ⊴ U` with `V ≤ P`, and let `C ≤ Z(P)` with `Z_R ≤ C`; for example
   `C = Z(P)`. Then `P/C` is not a finitely presented perfect group. In particular
   `P/C` is not a finitely presented simple group.

**Normal subgroups meeting V.** Thompson's `V` is simple, so a normal subgroup `P ⊴ U`
contains `V` as soon as `P ∩ V ≠ 1`. Examples are `U`, `[U,U]`, and the transport of
`E_3(R)` through a leaf-coordinate isomorphism `GL_3(R) ≅ U` whenever it is normal, since
it contains the image of the permutation matrices.

**When part 2 applies.**
- **Any simple ring of characteristic zero with a Leavitt family.** Its centre is a field
  containing `Q`, so `Z_R ⊇ Q^x`, which is not finitely generated. This includes every
  purely infinite simple ring `R ≅ R^2` of characteristic zero, since `R ≅ R ⊕ R` gives a
  Leavitt family.
- **Any algebra over an infinite field `K` with a Leavitt family.** `K^x` is never
  finitely generated: in characteristic zero it contains `Q^x`. In characteristic `p` it
  contains either infinitely many roots of unity, if `K` is algebraic over `F_p`, or
  `F_p(t)^x`, which has infinite rank.
- **Named cases:** `L_K(1,2)` for every infinite field `K`; the resolvent ring `R_L` of
  `leavitt-resolvent-ring-is-fp-simple-of-char-zero`; and `B ⊗ L_Q(1,2)` for every
  `Q`-algebra `B`.

## Consequence for `gl-n-q-embeds-in-fp-simple-group`

- **One recipe is dead.** A simple ring that contains `Q` has characteristic zero. So
  "take a simple ring with `Q` in it and a Leavitt family, then divide a normal
  `V`-containing subgroup of its units by the centre" never yields a finitely
  presented simple host.
- **This does not need the subgroup to be finitely presented, perfect or finitely
  generated.** So it kills the Khanh-style route, which proves finite presentation of the
  unit group and then divides out the scalars, before any K-theory is done.
- **What survives.**
  - subgroups of `R^x` that are not normal, or normal subgroups meeting `V` trivially;
  - quotients by non-central normal subgroups;
  - rings whose central units are finitely generated, e.g. `L_Z(1,2)` (central units
    `±1`). Such rings contain `Q` only group-theoretically, not as a subring, e.g.
    `integral-leavitt-unit-group-contains-q`.
