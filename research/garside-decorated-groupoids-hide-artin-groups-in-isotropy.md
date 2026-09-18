---
rg: 2
id: garside-decorated-groupoids-hide-artin-groups-in-isotropy
kind: claim
title: In the decorated Garside odometer full group of a finite-type Artin group, the Artin group sits mostly in the isotropy, and no simple subgroup contains it
distinct_from:
  decorated-garside-odometer-full-groups-are-type-f-infinity: that is Li's finiteness theorem for this full group, which stands; this computes the groupoid and shows the full group is useless as a simple host for the Artin group.
  artin-normal-form-boundary-full-groups-fix-a-point: that concerns the Belk--Bleak--Chatterji--Matucci--Perego normal-form boundary, where the Artin group acts faithfully; Li's monoid boundary used here is a different, one-point space.
artifacts:
  - research/artifacts/gq-bh-bh-free-15-2026-preprints.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed). This corrects the same
lane's landing aaf40d700.

## Setting

- `A` is a finite-type Artin group with at least two generators, `P = A^+` its
  positive monoid, and `ℓ : A → Z` the length homomorphism.
- `K = ker ℓ`, which is nontrivial: `ab^{-1} ≠ 1` for distinct generators `a, b`.
- `C_P`, `C = C_P × F_2^+ × F_2^+`, `D = C ⋈ Z` and `F_P ⊇ F_P^0` are as in
  `decorated-garside-odometer-full-groups-are-type-f-infinity`.
- Groupoids are Li's `I_l ⋉ ∂Ω`, whose germs are inverse-semigroup germs:
  `[s,χ] = [t,χ]` iff `se = te` for some idempotent `e` with `χ(e) = 1`.

## Statement

1. **The unit space.** Li's boundary `∂Ω_P` is a single point.
   - `∂Ω_{C_P}` is homeomorphic to `{0,1}^N`, the decoration only.
   - `X := ∂Ω_D = ∂Ω_C` is homeomorphic to `({0,1}^N)^3`.
2. **The groupoid.** `I_l(C_P) ⋉ ∂Ω_{C_P}` is isomorphic to the pullback
   `A ×_ℓ R_2` of the full 2-shift's Deaconu--Renault groupoid `R_2` along `ℓ`.
   - Its elements are pairs `(g, (y, n, y'))` with `ℓ(g) = n`.
   - Its isotropy at every point contains the open bisection `{(k, (y,0,y))}` for
     `k ∈ K`, so the groupoid is not effective.
3. **The embedding.** There is an injective homomorphism `B : A → F_P^0 ≤ F_P`.
   - Let `π : F_P → Homeo(X)` be the action on the unit space and `N = ker π`.
   - Then `B(A) ∩ N = B(K)`, and `π(B(A))` is infinite cyclic.
4. **No simple host.**
   - Every simple subgroup `S ≤ F_P` with `S ∩ N ≠ 1` lies in `N`. In particular
     no simple subgroup of `F_P` contains `B(A)`.
   - `D(F_P)` is not simple. This refutes
     `garside-odometer-groups-have-simple-finite-index-commutator`.

## Proof

1. **Unit space.**
   - In a Garside monoid any two elements have a common right multiple (both
     divide `Δ^n`), so `pP ∩ qP = (p ∨ q)P ≠ ∅`.
   - The constructible right ideals therefore form a filter, and the only maximal
     character is the one that is `1` everywhere. So `∂Ω_P` is a point.
   - For `C_P`, a boundary point is a maximal directed hereditary set of pairs
     `(p, w)`. Its `P`-part is all of `P`. Directedness forces all decorations `w_p`
     to be prefixes of one infinite word `y`: `w_p` and `w_q` are both prefixes of
     `w_{p∨q}`.
   - So `∂Ω_{C_P} = {0,1}^N`, with `λ_{(p,w)}` acting by `y ↦ wy`. Products of
     monoids give products of boundaries.
2. **The groupoid.**
   - For `p, q, p', q' ∈ P` and decorations, look at the germs of
     `s = λ_{(p,w)} λ_{(q,u)}^{-1}` and `t = λ_{(p',w')} λ_{(q',u')}^{-1}` at a common
     point. They have a common restriction iff two things hold:
     - `pq^{-1} = p'q'^{-1}` in `A`. On the `P`-coordinate, `s` and `t` act by left
       multiplication by these two group elements.
     - The prefix replacements `u z ↦ w z` and `u' z ↦ w' z` agree near the point,
       i.e. have the same lag. Garside lcms give the common refinement.
   - So a germ is exactly a triple `(y, g, y')` with `y = wz`, `y' = uz` and
     `|w| − |u| = ℓ(g)`. Every `g` occurs: replace `p, q` by `pΔ^j, qΔ^j` to make
     lengths as large as needed.
3. **The embedding.**
   - Let `h ∈ Homeo(X)` move the first digit of the second factor to the front of
     the decoration: `h(y, b x_2, x_3) = (b y, x_2, x_3)`.
   - For `g ∈ A` with `n = ℓ(g) ≥ 0`, write `g = p q^{-1}` with
     `ℓ(p) = ℓ(q) + n`. Let `B_g` be the union, over decoration prefixes `u` with
     `|u| = ℓ(q)` and second-factor prefixes `v` with `|v| = n`, of the germs of
     `λ_{((p, v̄u), ∅, ∅)} λ_{((q,u), v, ∅)}^{-1}`. Here `v̄` is `v` reversed.
   - The domains and the ranges both partition `X`. So `B_g` is a global compact
     open bisection with label `g` everywhere and underlying homeomorphism `h^n`.
   - For `n < 0`, put `B_g = B_{g^{-1}}^{-1}`.
   - Labels multiply and the underlying maps compose, so `B_g B_{g'} = B_{gg'}`.
     The label recovers `g`, so `B` is injective.
   - `π(B_g) = h^{ℓ(g)}`. So `B_g ∈ N` iff `g ∈ K`, and `π(B(A)) = ⟨h⟩ ≅ Z`.
   - `F_P^0 ≤ F_P`, because `I_l(C) ⋉ X` is an open subgroupoid of
     `I_l(D) ⋉ X` with the same unit space (Li, lemma after `lem:SC-->SD`).
4. **No simple host.**
   - **Simple subgroups.** `N` is normal, being a kernel. If `S` is simple and
     `S ∩ N ≠ 1`, then `S ∩ N = S`, so `S ≤ N`. Now `B(A) ∩ N = B(K) ≠ 1` and
     `B(A) ⊄ N`, since `π(B_a) = h ≠ id` for a generator `a`.
   - **`D(F_P)` meets `N`.** Fix `k ∈ K ∖ 1`.
     - Let `B_k^{[0]}` have label `k` on the third-factor cylinder `[0]` and be the
       unit elsewhere. It lies in `N`.
     - Let `σ ∈ F_P` swap the first digit of the third factor, with label `1`.
     - Then `[B_k^{[0]}, σ]` has label `k` on `[0]` and `k^{-1}` on `[1]`. It is a
       nontrivial element of `N ∩ D(F_P)`.
   - **`D(F_P)` is not inside `N`.** `π(D(F_P)) ⊇ D(V) = V ≠ 1`, where `V` is the
     label-`1` Thompson group of the third factor.
   - So `N ∩ D(F_P)` is a nontrivial proper normal subgroup of `D(F_P)`. ∎

## Reading

- Li's finiteness theorem for categories graded by a Garside monoid sees the
  monoid only through isotropy, because the monoid boundary of a Garside monoid
  collapses to a point.
- The effective quotient `π(F_P)` is a Brin--Thompson-type group with an odometer,
  and `A` reaches it only through `ℓ`.
- A Boone--Higman host along these lines needs a category or self-similar action
  in which `A` acts faithfully on the unit space. The Belk--Bleak--Chatterji--Matucci--Perego
  normal-form boundary `∂L` gives such an action, but no finiteness theorem for
  its full group is known.
