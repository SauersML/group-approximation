---
rg: 2
id: free-bit-components-are-central-iff-they-see-the-base
kind: claim
title: In an SFT extension over a rigid base, a fibre marginal is base-central whenever, in every base configuration, the sites it transfers to by local rules (thickened by 2D) determine the base point; a free switch whose thickened support does not determine the base gives a noncommuting family in dimension 2
invalidates:
  - absorbing-rope-readers-are-not-pointwise-rigid-via-prereqs
distinct_from:
  downhill-centrality-needs-no-data-rigidity: that proves centrality when a one-predecessor rule descends toward every site; this needs no direction at all, only that the transfer reach of the marginal sees the whole base point.
  extension-rigidity-is-base-centrality-plus-pointwise-rigidity: that reduces rigidity of an extension to (C_D) plus pointwise rigidity; this gives a sufficient condition for (C_D), and a matching obstruction.
  coupled-rope-reader-has-nested-one-bit-fibres: that proves pointwise rigidity of the coupled reader and leaves (C_D) open; this proves (C_D) for it.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
  - coupled-rope-reader-has-nested-one-bit-fibres
  - locally-finite-splittings-preserve-rigid-sft-compactifications
```
**ESTABLISHED** for Theorems A and B (lane proof, bh-invent-15, 2026-09-19; not reviewed). Both
hold in every dimension and over every field.
- **Corollary C is REFUTED** (09-19, by its author): see `cohen-rope-reader-is-not-quantum-rigid`.
  - (H1) holds.
  - (H2) is false as used. The digits the reader reads are data of the positional extension,
    not of the rigid base.
  - With Cohen's absorbing automaton the reader is not quantum rigid at any scale.
  - The corollary's argument is valid only relative to a frozen positional layer.
- **What this does to the tail route.** The route to (C_D) suggested by the coordinator (a free
  idempotent is "tail-measurable", so it commutes) has no operator meaning, because quantum
  families carry no measure. The notion that does the work is **visibility** (Theorem A).
- **A correction.** `absorbing-rope-readers-are-not-pointwise-rigid` is retracted: its
  counterexample overlooked the detour links now written out in the parent.

## Setting
- `Λ` is finitely generated. `Y ⊆ B^Λ` and `X ⊆ (B × F)^Λ` are SFTs whose rules fit in `D`-balls,
  and the base projection of `X` lies in `Y`.
- `E` is a `D`-quantum family of `X` on a vector space `W` over a field `k`, with (Q1)–(Q3) as in
  `fp-v-times-subshift-full-groups-force-quantum-rigidity` (so commutation holds within distance
  `2D`).
- Write `E^B_b(v)` for base marginals and `E^F_S(z) = Σ_{f∈S} E^F_f(z)` for fibre marginals,
  `S ⊆ F`. For a base pattern `π` on a finite window, `[π] = ∏_w E^B_{π(w)}(w)`.
- `Y` is `D`-quantum rigid over `k`.
- **Transfer steps.** A *transfer step* is a `D`-ball `P` with a base pattern `β` on it, sites
  `z, z' ∈ P`, and sets `S, S' ⊆ F` such that every pattern of `L_D(X)` on `P` with base `β` has
  `fibre(z) ∈ S ⟺ fibre(z') ∈ S'`. `S' = F` is allowed, meaning `z` is forced into `S`.
- **The reach.** For `y ∈ Y`, the *reach* `K_y(u, f)` is the set of sites `z` that can be joined
  from `(u, {f})` to some `(z, S)` by a finite chain of transfer steps whose base patterns are
  restrictions of `y`. The pair `(u, f)` is *forced under `y`* if some chain ends at `(z, F)` or
  `(z, ∅)`.

## Theorem A (visibility implies centrality)
Suppose that for every `y ∈ Y`, either `(u, f)` is forced under `y`, or `y` is the only point of
`Y` that agrees with `y` on the `2D`-neighbourhood of `K_y(u, f)`. Then `E^F_f(u)` commutes with
every base marginal. If this holds for all `(u, f)`, then (C_D) holds.

## Theorem B (invisible switches break centrality)
Suppose `x_0, x_1 ∈ X` lie over `y`, and `x'_0, x'_1 ∈ X` lie over `y' ≠ y`, such that:
- `x_0` and `x_1` differ exactly on a set `K`, and `x'_0, x'_1` differ exactly on `K` too;
- `x_i = x'_i` on the `2D`-neighbourhood of `K`, for `i = 0, 1`.

Then some `D`-family of `X` on `k^2` is not base-central.

## Corollary C (the coupled rope reader)
Assume (H):
- (H1) every base configuration of the `S_M` scaling seed has a unique sink, a coset or an end;
- (H2) a base configuration is determined by its labels on any set of row sites of its sink coset
  that is unbounded in both `x`-directions (finite sink), or by its labels on the spine cosets
  (end sink).

Then the reader of `coupled-rope-reader-has-nested-one-bit-fibres` satisfies (C_D). With part 4
there and the rigidity of the base seed, it is `D`-quantum rigid for all large `D`, over every
field, by item 3 of `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`.

## Proof of A
**Lemma 1 (a step is an identity).** For a transfer step:
`[β] E^F_S(z) = [β] E^F_{S'}(z')` and `E^F_S(z) [β] = E^F_{S'}(z') [β]`.
- By (Q2) all idempotents in `P` commute.
- By (Q3), summing over the other sites with (Q1), `[β] E_S(z) E_{F∖S'}(z') = 0` and
  `[β] E_{F∖S}(z) E_{S'}(z') = 0`.
- So `[β]E_S(z) = [β]E_S(z)E_{S'}(z') = [β]E_{S'}(z')`.
- Chains compose: if `π` is a base pattern on a window containing every step's ball, then
  `[π] = [π][β_j]`, so `[π]E^F_f(u) = [π]E^F_S(z)` for every `z` in the reach, and likewise on the
  right. A forced chain gives `[π]E^F_f(u) = c[π]` with `c ∈ {0, 1}`.

**Lemma 2 (patterns outside the language vanish).**
- The base marginals form a `D`-family of `Y`: (Q3) for a forbidden base pattern follows by summing
  over its fibre completions, all of which are forbidden. So they commute, since `Y` is rigid.
- They therefore generate a Boolean algebra `𝔅`. Every ultrafilter of `𝔅` gives a configuration all
  of whose `D`-patterns lie in `L_D(Y)`, so it lies in `Y`.
- Hence `[π] = 0` for every `π ∉ L_Ω(Y)` (Stone), and `Σ_{π ∈ L_Ω(Y)} [π] = 1`.

**The argument.** Fix `v`, a base letter `b`, and put `Π = E^B_b(v)` and `E = E^F_f(u)`.
- *Witnesses.* For each `y`, take either a forced chain, or finitely many reach sites
  `z_1, …, z_r` with their chains together with a finite `Ω_0 ⊆ N_{2D}(\{z_i\})` such that
  `y|_{Ω_0}` determines the letter at `v` in `Y`. The second exists by compactness: the set
  `{y' : y' = y on N_{2D}(K)}` is `{y}`, so some finite part of it already forces `y'(v) = y(v)`.
- *One window.* These witnesses are finite patterns, so finitely many of their cylinders cover
  `Y`. Let `Ω` be a finite window containing all of them together with `v`. Then every
  `π ∈ L_Ω(Y)` carries a witness.
- *The terms.* By Lemma 2, `Π E (1−Π) = Σ [π] E [π']`, over `π, π' ∈ L_Ω(Y)` with `π(v) = b ≠ π'(v)`.
  - If `π` is forced, `[π]E[π'] = c[π][π'] = 0`.
  - Otherwise `π` and `π'` differ at some `w ∈ Ω_0`. Otherwise `π'` would have letter `b` at `v`.
    Take `z_i` with `d(z_i, w) ≤ 2D`. Then
    `[π]E[π'] = [π]E_S(z_i)E^B_{π'(w)}(w)[π'] = [π]E^B_{π'(w)}(w)E_S(z_i)[π'] = 0`.
- *The other side.* `(1−Π)EΠ = 0` in the same way, using the witness of the left-hand pattern.
- So `ΠE = EΠ`. `∎`

## Proof of B
Put `W = k^2 = ke_1 ⊕ ke_2`, a `y`-sheet and a `y'`-sheet, and let `Q = [[1,1],[0,0]]`, an
idempotent that is not diagonal.
- **The family.**
  - Off `K`, every letter idempotent is `diag([x_0(z) = ·], [x'_0(z) = ·])`.
  - On `K`, the letter `x_0(z)` gets `Q`, the letter `x_1(z)` gets `1 − Q`, and all other letters
    get `0`. Base letters on `K` agree (`y = y'` there), so they are scalars.
- **(Q1)** is clear.
- **(Q2).** A site within `2D` of `K` but not in it carries scalars, since `x_0 = x'_0` there. So
  only diagonal matrices, or polynomials in `Q`, ever meet.
- **(Q3).**
  - A `D`-ball missing `K` gives `diag([x_0 = α], [x'_0 = α])`, which is 0 for forbidden `α`.
  - A `D`-ball meeting `K` lies inside `N_{2D}(K)`. There the product is a scalar times a product of
    `Q`s and `(1−Q)`s, which is nonzero only if `α` is the restriction of `x_0` or of `x_1`.
- **Failure of centrality.** At `v` with `y(v) ≠ y'(v)`, `E^B_{y(v)}(v) = diag(1,0)`, which does not
  commute with `Q`. `∎`

## Proof of C
Fibre letters are `(ρ, q)`. For every `y` and every site, one of three cases holds.
- **(T1)** The letter is forced by a finite deduction (anchored chains, a bad digit above, `ρ` fixed
  by a finite sink or by a region boundary). Then `(u, f)` is forced.
- **(T2)** `ρ` is free (end sink) and `q` is forced under `ρ = 1`.
  - Transfer steps along the deduction give `(u, {(1,s)}) ↦ (z, {ρ = 1})`. Good digits act as the
    identity on `{ok, bad}`; a bad digit forces `bad` at its own site.
  - The `ρ`-transport then carries this to every element of every spine coset.
- **(T3)** `u` is a free site (an all-good position in `R`). The detour steps of the parent carry
  `(u, {f})` to `(z, {f})` for every free site `z` of `R`.
  - A sideways step is a transfer step even though (L) needs `ρ = 1`: if `ρ = 0`, both sites carry
    `⊥`, since siblings share `ρ` with their parent inside one ball.

So in cases (T2) and (T3) the reach contains the spine cosets, or the free sites of the sink row,
which are unbounded in both `x`-directions. By (H2) this determines `y`, and Theorem A applies.

**About (H2).**
- Pointers are the tree directions to the sink.
- Layer M's markers and residues are transported coset to coset, in both directions.
- On the sink coset with free sites, `C_Z ⊠ C_Z` is pinned by `−` at row sites far left and far
  right, and by `*` along the row.

This is inspection of the rules in `modular-machine-scaling-seed-reads-regular-numerals`, not
written out rule by rule.

## For the seed tower
- **Step 1 of the build order is closed, modulo (H).** The coupled numeral reader is a rigid seed
  extension that marks any regular rope index set at linear radius.
- **Step 2 is next:** the rope relative seed over `K_M`, reading `v(x^α)`.
- **Design rule for every free mark,** including the halting-pair core mark of
  `halting-pair-seeds-need-a-two-sided-core-mark`. A free bit must be linked to the base's anchor
  (the sink or the spine). A bit whose linked support stays inside one coset, or one `E`-coset,
  while the base can vary elsewhere, gives a noncommuting family by Theorem B.

## Lesson for general BH
- **Centrality is visibility, not tails.** A free choice in an extension commutes with the base
  exactly when the sites it is locally tied to, thickened by `2D`, determine the base point.
- **Global freedom is harmless; local freedom is fatal.** A free bit linked to the anchor of a
  rigid seed is harmless: it is rigid and central. A free bit confined to a region that the
  base can change around breaks centrality in dimension 2.
- **For seed towers,** every reader and every mark may keep at most one choice at infinity, and
  that choice must be wired to the sink.
