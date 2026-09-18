---
rg: 2
id: fp-boolean-inverse-monoids-need-not-have-fp-full-groups
kind: claim
title: A finitely presented Boolean inverse monoid of a free ample groupoid can have a full group that is not finitely presented; the loss is exactly the non-commutative shadow of its idempotents
distinct_from:
  boolean-inverse-monoid-finite-presentation-is-finite-type: that says the monoid is finitely presented exactly for SFTs; this shows that its group of units need not be, for free SFTs that fail quantum rigidity.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that is the necessity theorem used here; this node supplies the explicit non-rigid free SFTs and reads the result as a failure of the units functor.
artifacts:
  - research/artifacts/gq-bh-bh-invent-03-groupoid-higman.md
---

**ESTABLISHED (lane proof, bh-invent-03, unreviewed; no priority claimed).** The proof is inline below.

**Statement.** Let `Λ` be an infinite finitely presented group carrying a free subshift of finite type
`Y_0 ⊆ B^Λ`; `Λ = Z^2` with any strongly aperiodic SFT works (Berger, Robinson). Let `|A| ≥ 2`,
`X = A^Λ × Y_0`, and `T = G_V × (Λ ⋉ X)`. Then:
1. the Boolean inverse monoid `B(T)` is finitely presented;
2. its group of units `F(T) = A(T)` is not finitely presented.

More generally, this happens for every free SFT over an infinite finitely presented `Λ` that fails
`D`-quantum rigidity for arbitrarily large `D` over some field.

**Proof.**
1. `X` is an SFT: its forbidden patterns are those of `Y_0` in the second coordinate. `Λ` acts freely
   on it because it does so on `Y_0`. So part 1 follows from
   `boolean-inverse-monoid-finite-presentation-is-finite-type`.
2. By `fp-v-times-subshift-full-groups-force-quantum-rigidity` (corollary), if `A(T)` is finitely
   presented then `X` is `D`-quantum rigid over every field for all large `D`. The equality
   `F(T) = A(T)` is `v-times-ample-full-groups-are-generated-by-transpositions`. We exhibit, for every
   `D`, a non-commuting `D`-quantum family over any field `k`.
   - **The family.** Fix `y ∈ Y_0` and `λ_0 ∈ Λ` with `d(1, λ_0) > 2D`. On `W_0 = k^2` take the
     non-commuting idempotents `P = diag(1, 0)` and `P' = (1 1; 0 0)`.
     - Put `P_0(1) = P`, `P_0(λ_0) = P'`, and `P_0(q) = I` for all other `q`.
     - Put `P_1(q) = I - P_0(q)`, and `P_a(q) = 0` for the other letters of `A`.
     - For a letter `(a, b)` of `A × B` put `E_(a,b)(q) = [b = y(q)] P_a(q)`.
   - **(Q1) holds.** At each site the `E_(a,b)(q)` are orthogonal idempotents summing to `I`.
   - **(Q2) holds.** Sites within distance `2D` include at most one of `1` and `λ_0`, and every other
     operator is `0` or `I`.
   - **(Q3) holds.** A pattern `(α_A, α_B)` absent from `X` has `α_B` absent from `Y_0`. Its product
     contains a factor `[α_B(f) = y(pf)] = 0`, because `y ∈ Y_0` shows the `B`-pattern of `y` at `p`
     does occur. So the product is `0`.
   - **It does not commute.** `E_(0,y(1))(1) = P` and `E_(0,y(λ_0))(λ_0) = P'`, and `PP' ≠ P'P`.

   So `X` is not quantum rigid at any scale, and `A(T)` is not finitely presented. `∎`

**Lesson for general BH.**
- **The units functor.** For ample groupoids, `B ↦ U(B)` (Boolean inverse monoid to full group) does
  not preserve finite presentation, even for free, purely infinite groupoids with a copy of `V`.
- **What is lost.** Only the axiom that idempotents commute is lost. The monoid presentation (F) forces
  all translated site idempotents to commute, while a group presentation must derive that commutation,
  and for `A^Λ × Y_0` it cannot. A full-shift factor gives independent far sites, whose idempotents can
  be quantized separately.
- **The right notion.** So "finitely presented ample groupoid", in the sense Boone–Higman needs, must be
  a finite Boolean-inverse-monoid presentation that is *rigid*: its algebra shadow must already force
  commutation. `rigid-boolean-inverse-monoid-presentations-have-fp-full-groups` states this notion and
  the conjecture that it suffices.
- **For the master route.** Freeness plus finite type (gate P1) is never enough. Quantum rigidity
  (gate G2) is the whole difference, and the simplest counterexamples are products with full shifts.
  - This is why minimality is required: a minimal SFT has no free full-shift factor.
  - The open question is whether minimality forces rigidity. That is gate G2(e), bh-g2-obstruct.
