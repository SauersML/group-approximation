---
rg: 2
id: quantum-rigid-subshifts-cluster-the-modifications-of-each-point
kind: claim
title: In a quantum-rigid subshift over any group, all modifications of a point meet within 2D and are carried along by its isotropy, so a point with infinite isotropy and a homoclinic partner rules out rigidity at every scale, and coinduction from a subgroup with infinitely many double cosets is never rigid
distinct_from:
  minimal-sfts-with-a-finite-modification-are-not-quantum-rigid: that states the far-modification lemma for SFTs and kills minimal SFTs with a finite modification; this proves the lemma for every subshift (finite type is never used) and adds the isotropy form, which needs no minimality and fires exactly at points with infinite stabilizer.
  quantum-rigid-sfts-over-products-have-a-single-free-branch: that confines modifications across the slabs of a product with a multi-ended factor; this confines the modifications of one point under its own stabilizer, over any group.
  free-sft-hosts-admit-no-finite-type-coding: that shows finite-type engines need attracting (contracting) isotropy; this shows quantum rigidity forbids scattering isotropy, such as an emitter with homoclinic neighbours, which is the complementary half of the same picture.
  stabilizer-engines-embed-in-every-branch-compactification: that shows the one-point (emitter) engine is never of finite type; this shows the emitter is never quantum rigid in any coding, while the two-point blow-up over Z passes the same test.
artifacts:
  - research/artifacts/gq-bh-star-b-adversarial-star-prime.md
---

**ESTABLISHED** (lane proof, elementary; bh-star-b, 2026-09-18; not reviewed; no priority claimed).

## Setting

- `Λ` is a finitely generated group with a finite symmetric generating set, word length `|·|`, the
  left-invariant metric `d(a, b) = |a^(-1) b|`, and balls `B_D`.
- `X ⊆ A^Λ` is a subshift (closed and invariant, **not necessarily of finite type**), with
  `(g.x)(h) = x(g^(-1) h)`.
- `D`-quantum families and `D`-quantum rigidity over a field `k` are defined by (Q1)–(Q3) of
  `fp-v-times-subshift-full-groups-force-quantum-rigidity`. (Q3) quantifies over the patterns on
  `B_D`-balls that occur in no point of `X`, so the definition makes sense for every subshift.
- For `x, y ∈ X`, `Δ(x, y) = {g : x(g) ≠ y(g)}`. A *modification* of `x` is any `y ∈ X \ {x}`.
- `Stab(x) = {h : h.x = x}`. Then `Δ(h.x, h.y) = h Δ(x, y)`, so `Δ(x, h.y) = h Δ(x, y)` for
  `h ∈ Stab(x)`.

## Lemma 1 (far modifications, any subshift)

Let `x, y_1, y_2 ∈ X` with `y_i ≠ x`, and put `Δ_i = Δ(x, y_i)`. If `d(Δ_1, Δ_2) > 2D`, then `X` is
not `D`-quantum rigid over any field.

*Proof.* Let `z` equal `y_i` on `Δ_i` and `x` elsewhere. It need not lie in `X`.
- **Local legality.** A ball `pB_D` has diameter at most `2D`, so it misses `Δ_1` or `Δ_2`. If it
  misses `Δ_2`, then `z = y_1` on it, because `y_1 = x` off `Δ_1`; symmetrically otherwise. So every
  `B_D`-pattern of `z` occurs in `X`.
- **The wall family.** Put `P = Δ_1`, `M = N_(2D)(Δ_1) \ Δ_1` and `N = Λ \ N_(2D)(Δ_1)`.
  - Then `x = z` on `M`, since `M` misses `Δ_2`; `x ≠ z` somewhere on `P` and somewhere on
    `Δ_2 ⊆ N`.
  - A pair of sites at distance `<= 2D`, and every ball `pB_D`, lies in `P ∪ M` or in `M ∪ N`.
- On `W = k^2`, let `E_a(q)` be diagonal with entries `([x(q) = a], [z(q) = a])`, in the basis
  `(e_1, e_2)` for `q ∈ P ∪ M` and in the basis `(e_1 + e_2, e_2)` for `q ∈ N`. On `M` these operators
  are scalars.
  - (Q1) holds.
  - (Q2) holds, because each close pair lies in one of the two regions, where everything is diagonal
    in one basis.
  - (Q3): on a ball inside one region, the product over a forbidden pattern `α` is
    `diag([x reads α], [z reads α])`, and both entries vanish, since `x ∈ X` and `z` is locally legal.
- **Noncommutation.** Take `q ∈ Δ_1` and `q' ∈ Δ_2` with `a = x(q) ≠ z(q)` and `b = x(q') ≠ z(q')`.
  In the standard basis, `E_a(q) = [[1,0],[0,0]]` and `E_b(q') = [[1,0],[1,0]]`. These do not commute,
  over any field. ∎

This is the proof of `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid` with one change:
its step "`z ∈ X` because `X` is an SFT with `D >= r`" is replaced by local legality at scale `D`,
which is all the wall certificate reads.

## Theorem (clustering)

Suppose `X` is `D`-quantum rigid over some field. Then for every `x ∈ X`:
1. **Clustering.** Any two modifications of `x` have supports at distance at most `2D`:
   `d(Δ(x, y_1), Δ(x, y_2)) <= 2D` for all `y_1, y_2 ∈ X \ {x}`.
2. **Isotropy.** For every modification `y` and every `h ∈ Stab(x)`,
   `d(Δ(x, y), h Δ(x, y)) <= 2D`.
3. **No homoclinic partner at infinite isotropy.** If `Stab(x)` is infinite, then no modification of `x`
   has finite support.

*Proof.* (1) is Lemma 1. For (2), apply (1) to `y` and `h.y`; this is a modification of `x`, because
`h.y = x` would force `y = x`. For (3), if `Δ` is finite, then `d(Δ, hΔ) <= 2D` forces
`h ∈ ⋃_(p,q ∈ Δ) p B_(2D) q^(-1)`, which is a finite set. ∎

Two consequences of (1):
- Taking `y = λ.x`: the non-periodicity sets `Δ(x, λ.x)`, for `λ ∉ Stab(x)`, are pairwise `2D`-close.
- For minimal `X`, uniform recurrence copies any finite modification far away, which recovers the
  theorem of `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`. Item (3) is the
  non-minimal analogue: the isotropy makes the far copy.

## Corollaries

1. **The obstruction does not depend on the coding.** Let `φ : X → X'` be a conjugacy onto a subshift
   over the same `Λ`, a sliding block code of radius `r`. Then `Δ(φx, φy) ⊆ N_r(Δ(x, y))`, and the
   same holds for `φ^(-1)`.
   - So "`Δ(x, y)` is finite" is the conjugacy invariant `lim_(g→∞) d(g.x, g.y) = 0`: `x` and `y` are
     *homoclinic*.
   - Hence: **if some point with infinite stabilizer has a homoclinic partner, then no subshift
     conjugate to `X` is `D`-quantum rigid, for any `D` and any field.** Neither minimality nor finite
     type is assumed.
2. **Scattering isotropy.** More generally, if some modification `y` of `x` satisfies
   `sup_(h ∈ Stab(x)) d(Δ(x, y), hΔ(x, y)) = ∞`, then `X` is not rigid at any scale.
   - An *emitter* is the typical case. `x` has infinitely many local branches permuted by
     `Stab(x)`, and `y` lies in one branch, with its support localized there.
   - Worked instances are `v-stabilized-stabilizer-engines-are-never-finitely-presented` and
     calibration row 2 below.
3. **Coinduction is never rigid.**
   - *Setting.* Let `Λ ≤ Λ'` with `Λ'` finitely generated and the double coset space `Λ\Λ'/Λ`
     infinite. Let `Y ⊆ A^Λ` be a subshift with at least two points. Put
     `CoInd Y = {x ∈ A^(Λ') : (λ ↦ x(hλ)) ∈ Y for every h ∈ Λ'}`.
   - *Claim.* `CoInd Y` is not `D`-rigid for any `D`.
   - *Proof.* Cosets `h_1Λ` and `h_2Λ` are within `2D` only if `h_1^(-1) h_2 ∈ Λ B_(2D) Λ`, a finite
     union of double cosets. So far-apart cosets exist. Changing the `Y`-point carried by one coset
     gives a modification supported in that coset. Two far cosets give Lemma 1.
   - *Where it applies.* The hypothesis holds when `Λ` is normal of infinite index, and when
     `Λ' = Λ * Z`.
   - *The escape.* It fails exactly in the finite double-coset regime of
     `finite-double-coset-space-with-free-minimal-coset-sft`, which stays open.
4. **Monotonicity.** A closed invariant subset of a `D`-rigid subshift is `D`-rigid, because it has more
   forbidden patterns. So the obstructions above also kill every subshift that *contains* the offending
   points.

## Calibration (no false kills; the positive cases pass)

| Subshift | Isotropy | Modifications of a fixed point | Test | Known status |
|---|---|---|---|---|
| full shift `A^Λ` | all of `Λ`, at constant points | finite | fails (3) | not rigid |
| `{x ∈ {0,1}^Z : at most one 1}` (one-point compactification of `Z`) | `Z` at `0^Z` | `δ_n`, finite | fails (3) | `[[Z ⋉ X]]` is Houghton's `H_2`, not finitely presented (Brown 1987, recalled) |
| `{x ∈ {0,1}^Z : x nondecreasing}` (two-point compactification) | `Z` at `0^Z` and `1^Z` | half-lines through the same end | passes | rigid at every `D ≥ 1` (check below) |
| end shift of `F_n` | cyclic, at axis ends `ξ` | geodesic lines ending at `ξ`, which share a ray | passes | rigid (`free-group-boundary-shifts-are-quantum-rigid`) |
| `∂T_m ⊠ ∂T_n` over `F_m × F_n` | `⊆ Z × Z` | `(line × F_n) ∪ (F_m × line)` through `(ξ, ζ)` | passes | rigid (`quantum-rigidity-is-product-stable`) |
| Ã₂ boundary skew shift | chamber stabilizers (periodic flats give `Z^2`) | contain an apartment through `ω`; apartments through `ω` share a sector | passes | rigid (`a2-lattice-boundary-skew-shifts-are-quantum-rigid`) |
| Ledrappier, permutive triangles | trivial | infinite cones | (1) only | rigid |
| stabilizer engine `X_B`, `B` infinite | `B` at vertex points | two edges | fails (3) | this node's sibling |

**Check of row 3.** The only forbidden word is `10`. Commuting operators on a ball sum to `I`, so (Q3)
gives `E_1(q) E_0(q+1) = 0`. Hence `E_1(q) = E_1(q) E_1(q+1)`, and with (Q2) `E_1(q)` is a
subprojection of `E_1(q+1)`. By induction `E_1(q) E_1(q+j) = E_1(q) = E_1(q+j) E_1(q)` for all
`j >= 0`. So every family commutes: this is a monotone chain, the one-dimensional case of compression.

Rows 2 and 3 are the whole point in miniature. The same group acts, with the same infinite isotropy.
The one-point compactification (an emitter) is killed. The two-point compactification (two ends) is
rigid. This matches `stabilizer-engines-embed-in-every-branch-compactification` 3(a)–(b): `Z⁺` is not
of finite type, and `Z ⊔ {±∞}` is.

## Lesson for general BH

**Quantum rigidity is a statement about how a point can be perturbed.**
- All perturbations of a point must meet, within `2D`.
- The point's isotropy must drag the perturbations along, never scatter them.

**Two kinds of fixed point.**
- *Ends*, the attracting fixed points of compression, pass: every perturbation shares a tail with every
  other.
- *Emitters*, parabolic points whose neighbours are homoclinic and permuted by the isotropy, fail at
  every scale, in every coding, with no finite-type or minimality hypothesis.

Together with `free-sft-hosts-admit-no-finite-type-coding`:
- finite type wants contracting isotropy;
- rigidity wants attracting modification clouds;
- emitters give neither.

**For the master route.** SYNTHESIS v5's alternative "a hard input sits at an infinite emitter" is
incompatible with (★′), on the ring route and the group route alike.
- A hard input must *scale*, acting freely, or sit at end-type points.
- The alternative is to blow the emitter up into an end-type compactification.
- **Independence kills rigidity.** Coinduction, independent cosets and independent branches all
  produce far modifications. So every gluing in a (★′) design must be total.
