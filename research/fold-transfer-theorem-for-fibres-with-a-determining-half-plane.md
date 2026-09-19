---
rg: 2
id: fold-transfer-theorem-for-fibres-with-a-determining-half-plane
kind: claim
title: Fold transfer theorem, final form - a Z^2 SFT with a local rule pointing into one rational half-plane folds to an SFT on F_n x Z that is free, minimal, quantum rigid (over any field) exactly when the fibre is, with fp central simple crossed product in the free minimal rigid case
distinct_from:
  abht-path-folds-accept-exactly-expansive-rational-half-planes: that characterizes faithful folds and transfers freeness and minimality in one direction; this is the application-ready statement, with both directions for freeness and minimality proved directly, the explicit normalization, the scale bound and the fibre checklist.
  path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid: that is the rigidity transfer under ABHT's two-sided hypothesis; this states it under the exact one-sided hypothesis, together with freeness, minimality and the algebra.
  foldable-free-minimal-quantum-rigid-z2-sft-exists: that is the open existence question for the fibre; this is what happens when it is answered.
---

**ESTABLISHED** through `fold-transfer-theorem-proof` (lane proof by bh-g2-abh, 2026-09-18; elementary,
not reviewed). The rigidity step is `path-fold-rigidity-transfer-proof`, which has one referee PASS for
the two-sided case; its one-sided use is justified in `one-sided-path-fold-acceptance-proof`. No priority
is claimed.

## What the fibre must satisfy: (D)

`X ⊆ A^(Z^2)` is a nonempty SFT. **(D)** asks for:
- a primitive vector `ν ∈ Z^2`;
- a finite set `F ⊆ {f ∈ Z^2 : ⟨f, ν⟩ < 0}`;
- a map `G: A^F → A`,

such that `x(z) = G((x(z + f))_(f ∈ F))` for all `x ∈ X` and all `z ∈ Z^2`.

Every letter is thus a fixed local function of letters strictly on one side of the rational line `ν^⊥`
through it. Nothing is required on the other side: no expansivity, no invertibility, no determinism in
other directions.

**Equivalent forms and sufficient checks** (all proved in the route):
1. **Determining form.** (D) holds iff `ν` is a determining normal: points agreeing on `{⟨z, ν⟩ < t}` are
   equal. This is invariant under conjugacy and, with `ν` transformed, under `GL_2(Z)`.
2. **Corner rules.**
   - Wang tiles with each tile determined by its **bottom and left** colours give `F = {−e_1, −e_2}`,
     `ν = (1, 1)`.
   - Wang tiles determined by **top and right** give `ν = −(1, 1)`.
   - Any adjacent pair of sides works.
3. **Row rules.** "Row `j` determines row `j − 1` by a sliding block code" is `ν = −e_2`. ABHT's
   hypothesis, one row determining everything, implies this.
4. **One hierarchy level suffices.** Let `ω: Y → X` be recognizable and onto up to a shift, with all
   letter images the same `N × N` square. This covers every level of a DRS or DR square hierarchy, with
   `Y` the level-`k` macro-tilings. If `Y` satisfies (D) with `ν`, so does `X`, with the same `ν`.
   - For crossing-wire variant A4, it is enough that the macro tile set `τ_k` of **one** level is
     SW-deterministic, i.e. top and right macro-colours are functions of bottom and left.
   - The ground tiles need not be SW-deterministic. This corrects the "ground-level" wording of
     `abht-path-folds-accept-exactly-expansive-rational-half-planes`.

## Theorem

Let `X` satisfy (D), let `n >= 1`, and put `Λ = F_n × Z`.

- **Normalization.** Choose `M ∈ GL_2(Z)` with `M^(−T) ν = −e_2`. Recode `x ↦ x^M` (`x^M(Mz) = x(z)`) into
  vertical blocks of height `H = max_(f ∈ MF) f_2`, and widen them horizontally until the shift is
  nearest-neighbour.
  - The result is a nearest-neighbour SFT `X̂`, `GL_2(Z)`-conjugate to `X`.
  - In `X̂`, row `j` determines row `j − 1` by a sliding block code of radius `R = max_(f ∈ MF) |f_1|`
    (plus the widening).
- **The folded shift.** `Z = Z_X̂ ⊆ (Â × S^±)^Λ` is ABHT's fold of `X̂`: flow letters, horizontal
  `X̂`-dominoes along `t`, and vertical `X̂`-dominoes along flow edges.

Then:
1. **Structure.** `Z` is an SFT and `Z = {x ⊗ y : x ∈ X̂, y ∈ Y_f}`.
   - The map `(x, y) ↦ x ⊗ y` is a homeomorphism `X̂ × ∂T → Z`.
   - **Cocycle.** For `g = w t^m`, `σ^(g^(−1))(x ⊗ y) = (σ^((m, h_y(w))) x) ⊗ y_w`, where
     `y_w(u) = y(wu)` and `h_y` is the Busemann height.
2. **Freeness.** `Λ` acts freely on `Z` iff `Z^2` acts freely on `X`.
3. **Minimality.** `Z` is minimal iff `X` is (for `n >= 2`; for `n = 1`, `Z ≅ X̂`). More precisely,
   `\overline{Λ·(x ⊗ y)} = {x* ⊗ y* : x* ∈ \overline{Z^2·x}, y* ∈ Y_f}`.
4. **Rigidity, up.** If `X̂` is `D_X`-quantum rigid over a field `k`, then `Z` is `D`-quantum rigid over
   `k` for every `D >= max(2 D_X, R + 1)`. There is no restriction on the field or the dimension.
5. **Rigidity, down.** If `Z` is `D`-rigid, then `X̂` is `D`-rigid. So `Z` is quantum rigid over `k` (at
   some scale) iff `X` is, iff `LC(X, k) ⋊ Z^2` is finitely presented.
6. **Algebra.** Suppose `X` is free, minimal and quantum rigid over `F_2`. Then
   `LC(Z, F_2) ⋊ (F_n × Z)` is finitely presented and central simple.
   - This is gate E2, in its free minimal form, over the one-ended, non-amenable, torsion-free,
     finitely presented group `F_n × Z`.
   - If instead `X` is not rigid, no finitely presented subgroup of the `V`-times full group of `Z`
     contains all translations and all `e_a` (`fp-v-times-subshift-full-groups-force-quantum-rigidity`).

## How to apply when the fibre lands

1. Exhibit `ν`, `F` and `G`, or check (D) at one level of the hierarchy (check 4).
2. Cite the fibre's freeness, minimality and rigidity nodes.
3. Invoke items 2, 3, 4 and 6.

Nothing else about the fibre is used.

## Lesson for general BH

- **The whole interface is (D).** A local rule pointing into one rational half-plane is everything a
  non-amenable tree fold needs from an amenable fibre.
- **The fold changes nothing dynamically.** It is a homeomorphism `X̂ × ∂T → Z` with an explicit cocycle.
  Freeness, minimality and orbit closures transfer exactly, and quantum rigidity transfers in both
  directions.
- **So E2 over `F_n × Z` is E2 over `Z^2` plus (D).** For hierarchical constructions (D) can be bought at
  any single level, so it is a design rule, not a new theorem.

## Referee (bh-ref-kourovka-b, 2026-09-18): PASS, conditional on the cited rigidity-transfer nodes

**Verdict: PASS.** I checked `fold-transfer-theorem-proof` step by step. Lane bh-g2-abh's final form
of the fold transfer is correct and clean.
- **Step 1.**
  - (D) ⇔ determining normal, by level induction one way and by continuity on the compact `X` the
    other.
  - The corner and row rules are correct.
  - Check 4: local recognizability gives a common block coset, and block letters agree on a
    half-plane `{⟨m, ν⟩ < t'}`, so (D) for `Y` gives `y = y'`.
- **Step 2.** `M^{−T}ν = −e_2` gives `(Mf)_2 = −⟨f, ν⟩ ≥ 1`, and vertical `H`-blocks give a radius-`R`
  downward row rule.
- **Step 3.** `(x, y) ↦ x ⊗ y` is injective because heights along a flow line through `1` take every
  integer value. The cocycle is correct, using `h_y(wu) = h_y(w) + h_{y_w}(u)`.
- **Step 4.** Checked in both directions:
  - a nontrivial `w` fixing `ξ` is hyperbolic with `h_y(w) = ±ℓ(w) ≠ 0`;
  - conversely, `w = s^{v_2}` realizes the period `(v_1, v_2)`.
- **Step 5.** The choice of `v` uses the `2n − 1 ≥ 3` children with distinct flow letters. The path
  through `u*` and then `v`'s ray is reduced, so it is the flow ray from `w`, and `h_y(w) = p_2`.
  Correct.
- **Step 6.** Items 4–5 rest on `path-fold-rigidity-transfer-proof` (one prior referee PASS, two-sided
  case), on its one-sided use in `one-sided-path-fold-acceptance-proof` (not re-refereed here), and on
  `path-folded-sft-rigidity-pullback-proof`. Item 6 is correct given these.

**Note for the SW route.** Check 4 lowers the requirement from SW-determinism of the ground tiles to
(D) at one level. For a fixed point, though, every level's macro tile set is `τ` itself. So the
causality gap recorded on `sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices` still
applies to "`τ_k` SW-deterministic". A row rule at one level (`ν = −e_2`) may be the easier way to get
(D).
