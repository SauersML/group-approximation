---
rg: 2
id: seeds-never-survive-marked-approximation
kind: claim
title: Over a finitely presented group no proper marked approximation carries any configuration containing a seed pattern; a seed makes its group isolated in the closed set of marked groups admitting the pattern, and for groups with a seed this relative isolation is equivalent to finite presentation
requires:
  - stabilizer-engines-are-fp-only-over-isolated-groups
distinct_from:
  stabilizer-engines-are-fp-only-over-isolated-groups: that is the approximation obstruction for emitter engines (fp engine ⇒ isolated vertex group); this shows the obstruction cannot be run on seed (finite-type) engines over fp groups, because approximating groups carry no seed configurations at all.
  stabilizer-engines-need-torsion-vertex-groups: that extends the emitter obstruction by collapsing deep subgroups; this concerns seeds, which that argument also needs to transport and cannot.
  decidable-groups-embed-in-rigid-sft-compactification-groups: that is the open (SEED) gate; this is a structural property every seed has, rigid or not.
---
**ESTABLISHED** (lane proof, bh-invent-15, 2026-09-18; elementary; not reviewed). Quantum
rigidity plays no role. Only (S1), an isolated seed point, and (S2), trivial stabilizer, are
used.

**Setting.** A **marked group** is `(Γ, Σ)` with `Σ` a finite generating tuple. `Y ⊆ A^Γ` is an
SFT given by a finite set `R` of forbidden patterns on a window `W ⊆ Ball(w)`. `p` is a
pattern on `Ball(w)` with `[p] ∩ Y = {y_*}` and `Stab(y_*) = 1`.
- **Rules over nearby groups.** For a marked group `Γ'` whose ball of radius `2w` is isomorphic
  to that of `Γ` (as labelled graphs), `R` and `p` make sense over `Γ'`, giving an SFT
  `Y(Γ') ⊆ A^{Γ'}`.
- **The admitting set.** Let `𝒮_{R,p}` be the set of marked groups in this neighbourhood such
  that `Y(Γ')` contains a configuration with `p` at `1`. By compactness it is closed in the
  space of marked groups.

## Theorem
1. **No seed survives over fp groups.** Let `Γ = ⟨Σ | Rel⟩` be finitely presented. There is an
   `r_0` such that every marked `Γ' ≠ Γ` agreeing with `Γ` on `Ball(r_0)` has **no**
   configuration of `Y(Γ')` containing `p`: not isolated, not free, not periodic, none at all.
2. **Relative isolation.** So `Γ` is an isolated point of `𝒮_{R,p}`.
3. **Converse.** If `Γ` is finitely generated but not finitely presented, then `Γ` is not isolated
   in `𝒮_{R,p}`, for any seed. The canonical approximations
   `Γ̂_L = ⟨Σ | relations of Γ of length ≤ L⟩` lie in `𝒮_{R,p}`: the pullback `ŷ_L` of `y_*` is
   a `p`-configuration. Its stabilizer is `M_L = ker(Γ̂_L → Γ) ≠ 1`, and its orbit is `Γ`, not
   `Γ̂_L`. So for a group with a seed, relative isolation ⟺ finite presentation.
4. **Consequence for the engine obstructions.** The transfer arguments of
   `stabilizer-engines-are-fp-only-over-isolated-groups` and
   `stabilizer-engines-need-torsion-vertex-groups` do not apply to finite-type (seed)
   blow-ups `F_S^K`, `K = \overline{S y_*}`, over finitely presented `S`.
   - Those arguments need engines of the same shape over approximating groups.
   - Such an engine needs a `p`-configuration with dense free orbit over the approximant, and
     by part 1 no approximant has one.
   - This is why the `C_Z` blow-up of Reid's group is finitely presented (Matui's `G_A`,
     SYNTHESIS v6 S2) although `Z` is not isolated.

## Proof
**1.**
- **Nearby groups are quotients.** Let `ℓ` be the longest relator and
  `r_0 = max(ℓ, 4w) + 1`. If `Γ'` agrees with `Γ` on `Ball(r_0)`, every relator holds in `Γ'`,
  so `Γ' = Γ/N`. Agreement on `Ball(r_0)` means `N ∩ Ball_Γ(r_0) = {1}`.
- **Pull back.** Suppose `z ∈ Y(Γ')` has `p` at `1`. Put `z̃(g) = z(gN)`. For every `g`, the
  quotient map is a label-preserving bijection `gBall(w) → gN·Ball(w)`, because
  `N ∩ Ball(2w) = 1`. So `z̃` has the same `W`-patterns as `z`, lies in `Y`, and has `p` at `1`.
- **Conclude.** Hence `z̃ = y_*`. But `z̃` is invariant under left translation by `N`:
  `(n·z̃)(g) = z(n^{-1}gN) = z(gN)`, since `N` is normal. So `N ≤ Stab(y_*) = 1`, and
  `Γ' = Γ`.

**2.** This is part 1 read in the space of marked groups: a neighbourhood of `Γ` meets
`𝒮_{R,p}` only in `Γ`.

**3.**
- **The canonical approximations are nearby.** `Γ̂_L → Γ` is injective on `Ball(⌊L/2⌋)`, and
  `Γ̂_L → Γ` in the space of marked groups. Also `Γ̂_L ≠ Γ` for every `L`, since `Γ` is not
  finitely presented.
- **They admit the pattern.** For `L ≥ 4w`, the pullback `ŷ_L(g) = y_*(ḡ)` satisfies `R` by the
  same local-bijection argument, and it has `p` at `1`.
- **What it sees.** `ŷ_L` is invariant exactly under `M_L`, because `Stab(y_*) = 1`. So its
  orbit is the `Γ̂_L`-set `Γ̂_L/M_L = Γ`.

**4.**
- **The obstruction needs tables over the approximant.** The obstruction transports tables of
  `F_S^K` to engines over approximants `S_n`. Those tables are Boolean combinations of shadows
  and of branch cylinders `[q]` of `K`, labelled by elements of `Z/k * S`.
- **The approximant must supply a matching blow-up.** It needs an `S_n`-compactification of
  `S_n` whose cylinder combinatorics matches `K` on the finitely many patterns used. That is,
  a point with `p` at `1`, trivial stabilizer and an open dense orbit.
- **None exists.** For finitely presented `S`, part 1 rules out even the first requirement.
  (For the collapse variant, `S *_H (H × Z/k)` with a deep `H`, the branch set at a vertex
  becomes `S/H`. Whether a seed-type compactification of `S/H` can match `K` is not examined
  here.)

## What this answers
- **Coordinator's question: can seed rigidity be approximated?** No, and not even seeds can be.
  Over a finitely presented group, a seed is a **local certificate that the group is not any
  of its proper approximants**.
- **The parallel with isolation.**
  - Isolated = finitely presented + finitely discriminable (Cornulier–Guyot–Pitsch).
  - Seeded + relatively isolated = finitely presented (parts 2–3).
  - So the seed replaces finite discriminability. It is exactly the finite-type
    substitute for isolation that the emitter obstruction demanded.
- **For CAP (v6 gate 1).**
  - Approximation arguments of the bb487abce / 58db3f3f9 kind can never prove CAP or refute
    (SEED). Every obstruction to finite presentation of seed engines must be non-local, for
    example via the word problem as in bh-g2-buildings' rigid route.
  - Conversely, seeds are not blocked by the approximation methods that kill emitters. So
    (SEED) is the right place to spend effort.
  - What remains open is whether fp + seed (no rigidity) already forces a solvable word
    problem. Finite discriminability does this for isolated groups by an r.e. certificate.
    The seed analogue would be a certificate for `w ≠ 1` from the uniqueness of `y_*`. It is
    not found here.
- **Track C residue (v6 gate 5).** For non-fp `S` the canonical approximations do carry
  `p`-configurations, but only with stabilizer `M_L` and orbit `S`. The transfer argument
  would need a `p`-configuration over `Γ̂_L` with trivial stabilizer and converging
  pattern language. Whether one exists is the exact question for bh-emitter-b's candidate
  "fp seed engine ⇒ fp vertex group". A yes kills the finite-type Track C for non-fp
  inputs; a no leaves it open.

## Lesson for general BH
- **Seeds cannot be approximated.** Over a finitely presented group, the configuration
  forced by a seed pulls back along any proper approximating quotient to a periodic
  configuration of the original SFT. Uniqueness and trivial stabilizer then kill the kernel.
- **So a seed is relative isolation.** Its group is the only nearby marked group carrying the
  pattern. For groups with a seed this is equivalent to finite presentation.
- **The division of labour.** Emitters fail finite presentation by approximation. Seeds are
  immune to approximation, so only a non-local argument, such as the word problem, can
  decide CAP.
