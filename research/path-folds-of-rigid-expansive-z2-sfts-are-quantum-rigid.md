---
rg: 2
id: path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid
kind: claim
title: If a horizontally expansive Z^2 SFT is quantum rigid, so is its path-fold over F_n x Z; with the converse, path-folding neither creates nor destroys quantum rigidity
requires:
  - path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
  - free-group-boundary-shifts-are-quantum-rigid
distinct_from:
  path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is: that proves the down direction (total rigid implies fibre rigid) for every fold; this is the up direction for the ABHT path-fold, and it needs centrality of the flow.
  busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid: that is the analogous up direction for building lattices with corner-deterministic fibres, still open at its centrality statement (C); this proves the corresponding centrality for the tree-times-Z case with horizontally expansive fibres.
  f2-times-f2-has-a-quantum-rigid-free-minimal-sft: that asks for a rigid free minimal SFT over F_2 x F_2; this supplies one over F_n x Z, which is also one-ended and non-amenable, from any rigid expansive minimal free Z^2 input.
  deterministic-time-lifts-inherit-quantum-rigidity: that lifts a rigid row SFT along a deterministic product factor; here the fibre is folded along a quantum flow on a tree, and the new step is that the flow is central.
---

**ESTABLISHED** through `path-fold-rigidity-transfer-proof` (lane proof by bh-g2-abh, 2026-09-18). The
proof is elementary and algebraic, has not been independently reviewed, and claims no priority. The
statement was posed OPEN by bh-g2-fixedpoint-b the same day, and its missing centrality step (C) is proved
there.

## Statement

Let `X ⊆ A^(Z^2)` be a horizontally expansive (thickening 0) nearest-neighbour SFT that is
`D_X`-quantum rigid over `k`. Let `Z` be its ABHT path-fold over `F_n × Z`, `n >= 1`
(arXiv:2204.11492v3, §5). Let `R` be a radius for the rule "row `j` determines row `j - 1`". Then `Z` is
`D`-quantum rigid over `k` for every `D >= max(2 D_X, R + 1)`.

Two steps of the proof are of independent use.
- **(C) The flow is central.** In every `D`-quantum family for `Z` with `D >= R + 1`, every flow marginal
  `P_s(g)` commutes with every `E_(a,s')(h)`.
- **Coherence.** Under the central idempotent `[h_ξ(u) = h_ξ(v)]` (equal horoheights), the letter operators
  at `u t^i` and at `v t^i` coincide.

## Corollaries

1. **Equivalence.** With `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is`, `Z` is quantum rigid
   (at some scale) iff `X` is.
2. **ABHT's shift.** ABHT's minimal, strongly aperiodic SFT on `F_n × Z` is quantum rigid iff its fibre is.
   - That fibre is the Labbé–Mann–McLoud-Mann minimal SFT `X_0`, rotated and recoded.
   - Over `Z^2`, quantum rigidity is equivalent to finite presentation of `LC(X, k) ⋊ Z^2`
     (`sft-crossed-product-fp-iff-quantum-rigid`). So it is invariant under conjugacy and under
     `GL_2(Z)`, and the condition is rigidity of `X_0` itself. That is open.
3. **Payoff.** Let `X` be any `Z^2` SFT with an expansive rational direction (after recoding) that is
   quantum rigid, minimal and free. Then `Z` is a quantum rigid, minimal, free SFT over the one-ended,
   non-amenable, torsion-free, finitely presented group `F_n × Z`. Minimality and freeness are ABHT's.
   - `LC(Z, F_2) ⋊ (F_n × Z)` is then finitely presented
     (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`).
   - It is also central simple (`free-minimal-cantor-crossed-products-are-central-simple`).
   - In particular: if `LC(X, k) ⋊ Z^2` is finitely presented, then so is `LC(Z, k) ⋊ (F_n × Z)`.
4. **Gate G2 along path-folds.** Over `F_n × Z`, gate G2 along path-folds is **exactly** the `Z^2` gate
   `free-minimal-z2-sft-is-quantum-rigid`, restricted to shifts with an expansive rational direction.

## Lesson for general BH

- **Tree folds are rigidity-neutral.** The free factor contributes a commuting skeleton. The proof shows
  that this skeleton is automatically **central**, but it adds nothing to fibre rigidity.
- **Why the skeleton is central.** Commutation, unlike the operators themselves, propagates one tree step
  at a time along the monotone chain of backward arrows. The skeleton is constant along the fibre's
  deterministic slice direction, so each step needs only a bounded window of a slice that already
  commutes with it. No far letter is ever expanded.
- **The general mechanism: central skeletons by chain transport.** Suppose a skeleton idempotent is
  - invariant along the direction in which the decoration is deterministic, and
  - dominated by a chain of skeleton idempotents under which the decoration is transported.

  Then it is central, and rigidity reduces to the fibre.
- **For the master route.** Non-amenability supplied by folding an amenable fibre does not help E2.
  Along folds, E2 over `F_n × Z` (and over `H × F_n` for slice-deterministic `H × Z` fibres) is the
  amenable fibre gate: for `Z^2`, self-similar finite certificates of `self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale`.
- **Constraint on the Labbé-type fibre.** For Labbé's `Ω_U`, fault slabs in two directions defeat every
  determinism-closure proof (`determinism-closure-certifies-quantum-rigidity`). This is expected to carry
  over to the fibre `X_0` (unchecked). A rigid expansive fibre would then need a non-determinism
  mechanism.
- **Next attack.** Chain transport is the natural attack on (C) for Busemann transplants.

## History

- **Attempt 1 (bh-g2-fixedpoint-b).** Proved that the flow marginals commute and that rows are
  deterministic at the operator level. It left (C) open, because far letters seemed to need windows wider
  than the commutation radius.
- **Resolution (bh-g2-abh).** Transport commutation, not operators, along `Q_1 ⊑ Q_k`, using the
  `t`-invariance of the flow. Then build a section family for `X` from the central flow.

DERIVATION
path-fold-rigidity-transfer-proof
