---
rg: 2
id: b3-center-first-normal-form-passes-the-germ-condition
kind: claim
title: On the Deligne boundary of B_3 = Mod(S_1^1) the generators are thin but the germ condition fails because <Delta> is not normal in the germ group B_3; writing the central Delta^2 as a leading letter repairs it, giving an F_infinity full germ extension of V with germ group B_3 over its center
distinct_from:
  deligne-forms-are-singular-on-commuting-parabolic-diagonals: that shows the Garside structures of B_n, n >= 5, are not thin; this is the thin case B_3, where the only failure is in the germ condition, and it is repairable.
  z2-free-z-lies-in-an-fp-full-germ-extension-of-v: that runs the germ-extension machine on Z^2 * Z with abelian germ groups Z^2; this runs it with a nonabelian germ group, B_3 over its center, and on a mapping class group.
  artin-normal-form-boundary-full-groups-fix-a-point: that shows the germ group of an Artin group at Delta^{-infinity} is a quotient of it in which Delta has infinite order; for B_3 this shows the germ map is injective and the Delta-germs form a non-normal subgroup of infinite index.
  germ-rate-homomorphism-tests-germ-extension-finiteness: that gives a necessary rate test for the germ condition; here every germ rate is 1, so the failure found here is invisible to that test.
  bhm-corollary-hosts-over-v-are-cover-centralizer-groups: that proves in general that at every singular point certified by Belk--Hyde--Matucci over V the germs commute with a power of the V-germ; this is a worked instance on a mapping class group. The Deligne language meets that necessary condition only with exponent a = 2 (germs commute with Delta^2 = tau_q^2), and still fails hypothesis (3). The center-first language meets it with a = 1 and passes.
  odometer-lift-central-extensions-of-v-subgroups-into-2v-tau: that already proves Boone--Higman for central Z-extensions of V-subgroups with boundary-trivial class, through the host 2V_tau; B_3 is such an extension of PSL_2(Z), and this gives the same conclusion through a germ-extension host instead.
artifacts:
  - research/artifacts/gq-bh-bh-free-51-garside-and-mosher-thinness.md
---

**ESTABLISHED** by `b3-center-first-germ-condition-proof` (lane proof, elementary, not
independently reviewed; no priority claimed).

## Setting

- `B_3 = ⟨σ_1, σ_2 | σ_1σ_2σ_1 = σ_2σ_1σ_2⟩`, with `Δ = σ_1σ_2σ_1`, and `z = Δ^2` generating
  the center.
- `B_3` is the mapping class group of the torus with one boundary component (recalled).
- The proper simples are `σ_1, σ_2, σ_1σ_2, σ_2σ_1`. Here `x → y` if and only if `y` begins
  with the last letter of `x`.
- **The two languages.**
  - `L_Δ` is the Belk--Bleak--Chatterji--Matucci--Perego (BBCMP) Deligne normal form (§2.3,
    read at source). Its words are `Δ^k x_1 ⋯ x_n` with `k ∈ Z`, written with `Δ` or `Δ^{-1}`
    letters, and `x_1 → ⋯ → x_n` proper simples.
  - `L_z` has words `z^k Δ^ε x_1 ⋯ x_n`, with `k ∈ Z`, `ε ∈ {0,1}`, and `x_i` as before, over
    the alphabet `{z, z^{-1}, Δ}` together with the proper simples.

## Statement

1. **Both are thin.** On `∂L_Δ` the singular set of `σ_1` and of `σ_2` is `{Δ^{+∞}, Δ^{-∞}}`,
   and `Δ` is a prefix replacement everywhere. On `∂L_z` the singular set of `σ_1`, `σ_2` and
   `Δ` is `{z^{+∞}, z^{-∞}}`, and `z` is a prefix replacement everywhere. In both cases the
   action of `B_3` is faithful.
2. **L_Δ fails the germ condition.** Let `γ` be the germ map at `p = Δ^{+∞}`. Then:
   - `γ` is injective on `B_3`;
   - `γ(⟨Δ⟩)` is neither normal nor of finite index in `γ(B_3)`.

   Consequently, after any recoding into Thompson's `V`, the germ group `(V)_p ≅ Z` is
   neither normal nor of finite index in `(Γ)_p`. So Belk--Hyde--Matucci
   `cor:MainFinitenessCorollary`, hypothesis (3), fails for this structure, in both of its
   branches.
3. **L_z passes.** Recode `∂L_z` with complete binary prefix codes giving the `z`- and
   `z^{-1}`-loops primitive, cyclically distinct code words. Let `Γ` be the full germ
   extension of `V` from `prefix-replacement-actions-recode-into-germ-extensions-of-v`. Then:
   - `sing(Γ)` is the union of the `V`-orbits of `z^{±∞}`;
   - at `p = z^{±∞}`, `(Γ)_p ≅ B_3` and `(V)_p = Z(B_3)`;
   - so `(Γ)_p/(V)_p ≅ PSL_2(Z)`, which has type `F_∞`.

   Hence `Γ` has type `F_∞`, it is full and clopen transitive, and it has a type (A) action.
   So `B_3` lies in `B_A` through the germ-extension machine.

## Why it matters

- **Seifert-type centers are not an obstruction.** `B_3` is virtually `F_2 × Z`.
  `automatic-groups-embed-in-corner-germ-extensions` records that product normal forms make a
  commuting factor singular along the other factor's whole boundary. Item 3 shows the cure
  when the commuting factor is central: write it first. This is the instance, for one
  mapping class group, of the general constraint in
  `bhm-corollary-hosts-over-v-are-cover-centralizer-groups` (b). The center then acts by a shift of
  the leading block, its direction contributes two singular points, and the germ group
  there is the whole group over its center.
- **A new failure mode.** Item 2 is a failure of normality, not of rates: every germ rate at
  `p` is `1`. So the rate test of `germ-rate-homomorphism-tests-germ-extension-finiteness` is
  not sufficient. The remedy, forced in general by
  `bhm-corollary-hosts-over-v-are-cover-centralizer-groups` (b), is to make the base germ at
  each singular point the germ of a central element of its stabilizer.
- **Mapping class groups.** This is the first run of the machine on a mapping class group
  with a nonabelian germ group. Boone--Higman for `B_3` is already known, since it is linear;
  the value is methodological.
- **What does not carry over.** For `F_2 × F_2`, which lies in `Mod(S_g)` for `g ≥ 2`, neither
  factor is central. There, both lockstep structures
  (`deligne-forms-are-singular-on-commuting-parabolic-diagonals`) and sequential
  ones fail thinness. That is the crux left open.

## Lesson for general BH

- **The germ condition forces a central shift.** By
  `bhm-corollary-hosts-over-v-are-cover-centralizer-groups` (b), every germ that
  Belk--Hyde--Matucci certify over `V` commutes with a power of the period shift at its point.
  Its normal clause needs exponent `a = 1`: the shift letter itself must be central in the
  stabilizer germ group.
  - In the Deligne language the shift is `Δ`, and germs commute only with `Δ^2 = τ_q^2`.
    So (b) holds with `a = 2`, yet both clauses of hypothesis (3) fail.
  - So (b) is necessary but not sufficient. What a normal-form boundary must supply is a
    shift letter that is central in its stabilizer, not merely a central power.
  - Writing the central power first repairs it.
- **For BH itself this is not new.** Central extensions are already covered by
  `odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`.
- **The real limit is the rank.** Rank-one hosts absorb exactly the virtually central cyclic
  directions of stabilizers. Non-central commuting directions produce Cantor sets of phase
  singularities (`deligne-forms-are-singular-on-commuting-parabolic-diagonals`), and need
  higher-rank hosts.
