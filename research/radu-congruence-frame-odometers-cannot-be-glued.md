---
rg: 2
id: radu-congruence-frame-odometers-cannot-be-glued
kind: claim
title: In any almost action of Radu's arithmetic quotient, a vertex group of the second tree acting through second-prime congruence levels pays a uniform defect on the inversion relations, so frame microstates cannot be congruence towers
distinct_from:
  expanding-matchings-need-a-shared-stabilizer: that is the dyadic pair PSL_2(Z) < PSL_2(Z[1/2]) with two vertex orbits, where congruence models at both vertices are needed, and noncoincidence comes from unipotent valuations; this is the quaternionic lattice Q with one vertex orbit and an inversion, so congruence at one vertex already costs the defect, and noncoincidence comes from nondiscreteness of Q on T' with no matrix computation. Lemma G is imported from there unchanged
  radu-square-lamp-forces-reflections-in-finite-actions: that excludes genuine finite Q-actions with an exactly C_chi-invariant colouring; this excludes almost actions of Q whose vertex-group part is close to second-prime congruence, whatever the action of x is, and uses no colouring
  radu-horizontal-lattice-expands-on-finite-actions: that asks for a Cheeger constant of C_chi on all finite Q-actions, which needs the congruence subgroup property; this uses the gap only on the second-prime principal congruence quotients of the vertex group, which is the recalled congruence input
  radu-second-prime-frame-dynamics-admit-microstates: that is the open microstate statement; this settles its unchecked "approximate gluing" bullet negatively for congruence towers, and leaves it open
---

**ESTABLISHED (unreviewed), modulo the cited congruence gap `(τ_𝔮')` below.** Symbolic-dynamics lane,
sw-089.

**Setting.** `Q ≤ PGL_2(F_𝔮) × PGL_2(F_(𝔮'))` is the arithmetic quotient of
`radu-horizontal-quotient-is-arithmetic-lattice`, acting faithfully on the second tree `T'` (valence 3).
`p ∈ T'` is the vertex fixed by `<xz, xyx> ≅ S_3`, and `x` inverts the edge `e' = [p, xp]`. Put

```text
C_0 = Fix_Q(p)  (⊇ C = <a,b,c>),     B = Fix_Q(p) ∩ Fix_Q(xp),     φ(s) = xsx  (s ∈ B),
N_M = Fix_Q(ball B(p,M))  (M ≥ 0),   the principal 𝔮'-adic congruence subgroup of level 𝔮'^M of C_0.
```

`C_0` is the `{𝔮}`-arithmetic vertex group, `B` has index 3 in it and is normalized by `x`, and
`Q = C_0 *_B (B ⋊ <x>)`. Fix finite generating sets `S_C` of `C_0` and `S_B` of `B`.

**Input `(τ_𝔮')` (cited, not re-derived).** There is `κ > 0` with `max_(c ∈ S_C) ||cf − f|| ≥ κ||f||`
for every `M` and every `f ∈ ℓ^2(C_0/N_M)` of mean zero. The graphs `N_M\T_h` are congruence quotients
of the Bruhat–Tits tree at `𝔮` for the totally definite quaternion algebra over `Q(√17)`. Via
Jacquet–Langlands and a Ramanujan-type bound at `𝔮` for parallel-weight-2 Hilbert modular forms, their
nontrivial adjacency spectrum lies in `[−3, 2√2]`. Any positive Ramanujan exponent suffices. This is the
"congruence actions" bullet of `radu-horizontal-lattice-expands-on-finite-actions`.

1. **Noncoincidence (proved, elementary).** For `(M, M') ≠ (0,0)`, `B ∩ N_M ≠ B ∩ xN_(M')x`. The proof
   uses only four facts: `Q` acts faithfully and vertex-transitively on `T'`, `C_0` is infinite, and `C_0`
   is transitive on the star of `p`.
2. **Gluing defect.** There is `h > 0`, depending only on `S_C`, `S_B`, with the following property.
   Let `V` be a finite set with an action `ρ` of `C_0` all of whose orbits are of the form `C_0/N_M`
   (levels and multiplicities arbitrary), and let `X ∈ Sym(V)` be arbitrary. Then

   ```text
   Σ_(s ∈ S_B) |{v : X ρ(s) v ≠ ρ(φ(s)) X v}|  ≥  h · |{v : v lies in an orbit of level M ≥ 1}|.   (R1)
   ```

   The only free gluing is between `C_0`-fixed points.
3. **Robust form.** Let `σ : Q → Sym(V)` be `(F, ε)`-multiplicative, with `F` containing `x`, `S_C`
   and the words below. Suppose `σ|_(C_0)` is `δ`-close on `S_C` to a congruence action `ρ` as in 2.
   Then `h · |{level ≥ 1}| ≤ O_S(ε + δ)|V|`.
4. **Frame microstates are not congruence towers.** There is `δ_* > 0`, independent of the lattice `Λ`,
   of `N` and of the depth, with the following property. Let `Λ ≤ PGL_2(F_(𝔮'))` be torsion-free and
   cocompact, and let `(σ, y)` be an `(F, ε)`-microstate `(HV1)` for `Q ↷ PGL_2(F_(𝔮'))/Λ`
   (`homogeneous-quotient-soficity-gives-vertex-soficity`), with `F` large and `ε` small (depending on
   `Λ` only through a displacement constant). Then `σ|_(C_0)` is at Hamming distance `≥ δ_*` on `S_C`
   from every union of principal congruence `C_0`-sets.
   * *Towers excluded.* This covers the depth-`M` frame sets `K_p(M)\L/Λ`, which are exactly such
     unions, glued by any permutation modelling `x`.
   * *What a microstate must have.* A macroscopic proportion of its `C_0`-orbits must be non-congruence,
     or of mixed level involving other primes, and the corresponding diagonal `B`-orbits must fail the gap.

**Dictionary (symbolic dynamics → Radu).**

| Symbolic dynamics | Radu frame system |
|---|---|
| odometer `Z ↷ Z_2` | `C_0 ↷ K_p`-orbits of `L/Λ` (a profinite translation system) |
| Kakutani–Rokhlin towers of the odometer | depth-`M` frame sets `C_0/N_M` |
| gluing towers along an orbit equivalence | the model `X` of the inversion `x`, with `x B x = B` twisted by `φ` |
| a free extension of tower models | Lemma G. It works only on coincident diagonal orbits, and only level 0 coincides |

**Where the dictionary breaks.** The odometer tower method builds models by exact tower actions plus
an arbitrary gluing. For `Q` the gluing relation `xsx = φ(s)` is spectral, not combinatorial. The graph
of `X` occupies at most half of each noncoincident diagonal `B`-orbit, and property `(τ_𝔮')` makes that
half pay. So the break is at the gluing step, and it is uniform in depth.

**Model tests.**
* *Calibration against the dyadic node.* The same mechanism reproduces `(G2)` of
  `expanding-matchings-need-a-shared-stabilizer`.
* *Free product.* For `C_0 *_B` without the relation `xsx = φ(s)`, for instance `C_0 * <x>`, every
  congruence model glues freely and `(R1)` says nothing, correctly.
* *Genuine finite `Q`-sets.* A genuine action has zero defect. So `(R1)` forces every genuine finite
  `Q`-set whose `C_0`-orbits are pure `𝔮'`-levels to be `C_0`-trivial. That is right: `C_0` and `xC_0x`
  generate `Q`, and `𝔮'` is inverted in `Q`, so no finite quotient sees a nontrivial `𝔮'`-level.

Proof in `radu-congruence-frame-odometers-cannot-be-glued-proof`.
