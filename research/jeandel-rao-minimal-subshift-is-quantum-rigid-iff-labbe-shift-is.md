---
rg: 2
id: jeandel-rao-minimal-subshift-is-quantum-rigid-iff-labbe-shift-is
kind: claim
title: The Jeandel-Rao minimal subshift, Labbé's 19-tile shift and ABHT's minimal free SFT on F_n x Z are quantum rigid together or not at all; all three are decided by the single scale-2 question J_2(Ω_U) = 0
distinct_from:
  labbe-shift-is-quantum-rigid-iff-rigid-at-scale-two: that fixes the scale at which Ω_U is decided; this shows that the Jeandel-Rao minimal subshift and ABHT's F_n x Z shift are decided by the same question.
  labbe-wang-shift-crossed-product-is-finitely-presented: that is the open question for Ω_U; this adds nothing to its truth value and shows it is also the E2 question over F_n x Z along ABHT's fold.
  path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid: that reduces the fold to its fibre for any rigid expansive fibre; this identifies ABHT's actual fibre, up to Kakutani equivalence, with Labbé's shift.
---

**ESTABLISHED** (lane proof by bh-g2-abh, 2026-09-18, not reviewed). It combines imports with landed lane
proofs; each step is cited below. The truth value of the common question is **not** decided here.

## Statement

Let `k` be any field. Put:
- `X_0` for the Jeandel–Rao minimal subshift;
- `Ω_U` for Labbé's 19-tile shift;
- `Z` for ABHT's minimal, strongly aperiodic SFT on `F_n × Z` (`n >= 1`, arXiv:2204.11492v3, §5), built on
  the fibre `X_0`.

The following are equivalent.
1. `LC(X_0, k) ⋊ Z^2` is finitely presented. Equivalently, `X_0` is quantum rigid over `k`.
2. `LC(Ω_U, k) ⋊ Z^2` is finitely presented. Equivalently, `Ω_U` is quantum rigid over `k`.
3. `J_2(Ω_U) = 0` over `k`. That is, every family of 19-tile idempotent partitions, in any dimension, that
   commutes at sup-distance `<= 4` and kills the non-occurring `5×5` patterns, commutes.
4. `Z` is quantum rigid over `k`.

The same equivalence holds for each intermediate shift `X_1, …, X_4, Ω_5, …, Ω_12` of Labbé's chain.

## Proof

- **(1) ⟺ (2).** Follow the chain of
  `jeandel-rao-minimal-subshift-is-morphic-image-of-labbe-shift`:
  `X_0 ← X_1 ← X_2 ← X_3 ← X_4 ≅ Ω_5 ≅ Ω_6 ← Ω_7 ← … ← Ω_12 ≅ Ω_U`.
  - **Morphism steps.**
    - Each `ω_i` with `i <= 3` is recognizable in `Ω_(i+1)`, hence in `X_(i+1)`. By definition,
      `X_i = ∪_k σ^k ω_i(X_(i+1))`.
    - Each `ω_i` with `6 <= i <= 11` is recognizable and onto up to a shift.
    - So every morphism step is a Kakutani equivalence (`recognizable-morphisms-give-kakutani-equivalent-z2-groupoids`,
      items 1–2).
  - **Other steps.** `ȷ` is a conjugacy onto `X_4`, `η` is a shear (`GL_2(Z)`) conjugacy, and the
    equivalence `Ω_12 ≅ Ω_U` is a letter renaming. Each gives an isomorphism of transformation groupoids.
  - **Conclusion.** Finite presentation of `A_k` transfers along every step
    (`steinberg-fp-is-a-kakutani-invariant`, item 2). Both ends are SFTs: `X_0` by LMM and by Step 4 of
    the morphism proof, `Ω_U` as a Wang shift. So "finitely presented" is "quantum rigid"
    (`sft-crossed-product-fp-iff-quantum-rigid`).
- **(2) ⟺ (3).** This is `labbe-shift-is-quantum-rigid-iff-rigid-at-scale-two`.
- **(1) ⟺ (4).** ABHT's fibre `X` is conjugate to a higher-block recoding of `X_0`, rotated by `π/2`.
  - The rotation `x'(Rp) = rot(x(p))` is a `GL_2(Z)`-conjugacy, so `LC(X, k) ⋊ Z^2 ≅ LC(X_0, k) ⋊ Z^2`.
  - `X` is a horizontally expansive (thickening 0) nearest-neighbour SFT, so both fold theorems apply.
    - **Up:** `path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid` gives `X` rigid ⇒ `Z` rigid.
    - **Down:** `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is` gives `Z` rigid ⇒ `X` rigid. ∎

## Consequences

- **E2 over `F_n × Z` is Labbé's computation.** Item 1 of SYNTHESIS v4 (ABHT's shift on `F_n × Z`) and
  item 2 (the Labbé/DRS scale certificate) are now the same question, in its Labbé case. The question
  is `J_2(Ω_U) = 0`, which bh-g2-labbe is computing. No separate computation for `X_0` or `Z` is needed,
  and this lane ran none.
- **If `J_2(Ω_U) = 0` over `F_2`:**
  - `Z` is a quantum rigid, minimal, free SFT over the finitely presented, one-ended, non-amenable,
    torsion-free group `F_n × Z`.
  - `LC(Z, F_2) ⋊ (F_n × Z)` is then finitely presented (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`)
    and central simple (`free-minimal-cantor-crossed-products-are-central-simple`).
  - The Jeandel–Rao minimal crossed product is also finitely presented.
- **If there is one non-commuting scale-2 family for `Ω_U` over `k`:**
  - None of `X_0`, `Ω_U`, `Z` is quantum rigid at any scale.
  - By `fp-v-times-subshift-full-groups-force-quantum-rigidity`, none of their `V`-times full groups has a
    finitely presented subgroup containing all translations and all `e_a`. In particular gate P2 fails
    at all three.
- **Fault normals do not transfer.**
  - `determinism-closure-certifies-quantum-rigidity` kills determinism proofs for `Ω_U` in every
    **recoding** (block conjugacy), not across the non-uniform morphisms of this chain.
  - `X_0` has an expansive vertical direction. Its horizontal Conway worm (LMM p. 4: the rows `9/0`
    against `1/6`) gives one fault normal.
  - LMM describe worms along the nonexpansive directions (abstract). If worms occur along two
    non-parallel directions, determinism fails for `X_0` too. This was not checked beyond the abstract.
- **The edge-family criterion does not apply here.** The criterion of
  `fixed-point-wang-tile-rigidity-is-edge-family-commutation` (scale 0) needs a side-local
  self-simulation. Neither `Ω_U`'s `ω` (letter-dependent shapes) nor the chain provides one, so the
  decision scale stays 2.
  - Its edge-wall test is still a cheap first-order screen for the Labbé lane.
  - It would refute rigidity only after an analogue of that node's substitution step (item 2) for
    recognizable non-side-local morphisms. That analogue is open.

## Lesson for general BH

- **E2 is a Kakutani-class question.** Choose, within one class, the model that has the geometry needed
  for the construction, then decide rigidity on the model where the finite check is smallest.
  - Here the construction (folding onto the non-amenable group `F_n × Z`) needs an expansive rational
    direction. `X_0` has one; `Ω_U` does not.
  - The rigidity check (scale 2, 229 patterns) lives on `Ω_U`, where the self-similarity collapses the
    scale.
- **Two master-route gates were one gate.** E2 over a one-ended non-amenable group and the `Z^2` rigidity
  certificate are the same question.
- **Where the swarm should invest.** The single open computation `J_2(Ω_U) = 0` now carries the first
  non-amenable instance of E2. Proof or refutation effort belongs there, or in a different Kakutani class,
  not in more folds.

## Attempts

None beyond the reduction. By the coordinator's instruction, this lane did not duplicate bh-g2-labbe's
`J_2` computation.
