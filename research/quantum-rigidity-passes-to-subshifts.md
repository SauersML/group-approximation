---
rg: 2
id: quantum-rigidity-passes-to-subshifts
kind: claim
title: Every subshift of a D-quantum-rigid subshift over the same alphabet is D-quantum rigid, so a rigid seed is exactly a seed carved out of some rigid ambient SFT by extra rules
distinct_from:
  deterministic-extensions-of-rigid-sfts-are-rigid: that enlarges a rigid SFT by a deterministic layer; this shrinks one by extra rules, which never costs rigidity, and records that deterministic layers are finite-state relative to their base.
  quantum-rigidity-is-product-stable: that combines rigid factors over a product group; this is monotonicity of rigidity under inclusion over one group.
  decidable-groups-embed-in-rigid-sft-compactification-groups: that is the open (SEED) gate; this reduces its rigidity clause to finding a seed inside any rigid SFT over the overgroup.
---

**ESTABLISHED** (lane bh-star-a, 2026-09-18; elementary; not reviewed; no priority claimed). Quantum
families and (Q1)–(Q3) are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`. In
particular, (Q3) asks the product over `pB_D` to vanish for every pattern on `B_D` that **does not
occur** in the subshift.

## Statement

Let `Λ` be finitely generated, and let `X' ⊆ X ⊆ A^Λ` be subshifts over the same alphabet. If `X` is
`D`-quantum rigid over a field `k`, then so is `X'`.

*Proof.*
- A pattern that does not occur in `X` does not occur in `X'`. So every `D`-quantum family for `X'`
  satisfies (Q3) for `X`.
- (Q1) and (Q2) do not mention the subshift.
- Hence every `D`-quantum family for `X'` is one for `X`, so it commutes. ∎

## Consequences

1. **Carving.** Rules may be added freely. In particular, `Λ ∈ 𝒞` iff some SFT `Y` with a seed (S1–S3)
   is contained in some SFT `X` over `Λ` that is quantum rigid over every field at all large scales.
   So the rigidity clause of (SEED) is a property of the **ambient**, and the seed clause is a
   combinatorial carving problem inside it.
   - Examples: the block rules of `torsion-free-tree-product-lattices-lie-in-the-rigid-seed-class`, and
     the sink/pointer rules of `bs12-rigid-seed-is-its-normal-form`.
2. **What the ambient must be.** Rigidity is not free: the full shift over an infinite group is not
   rigid (a single free layer admits noncommuting slot families,
   `free-rewritable-tape-layers-kill-finite-presentation`). So CAP, restricted to rigid seeds, asks:
   > can a quantum-rigid SFT over a finitely presented group with hard word problem contain a seed?
3. **Deterministic layers are complexity-neutral.** Item 3 of
   `deterministic-extensions-of-rigid-sfts-are-rigid` says a point of a deterministic extension is
   determined by its base point and one fibre letter. Along any path the fibre letter is a
   finite-state transduction of the base point.
   - So over a seed `(Y, y_*)` the extension adds at most `|F|` lifts of `y_*`. Evaluating the fibre
     along a word costs a finite automaton on top of evaluating `y_*`.
   - The extension's rules include the base rules, so every base contradiction is an extension
     contradiction. Hence the seed-collapse function `κ(n)` of `seeded-groups-have-solvable-word-problem`
     can only decrease under a deterministic extension.
   - So deterministic extensions give rigid ambients for free, but they cannot by themselves raise the
     complexity a seed carries.
   - A cellular-automaton space-time layer is not of this form: its transport reads neighbouring fibre
     letters, not only the base. Rigidity of such layers is the separate question of
     `permutive-triangle-sfts-are-quantum-rigid` (three semi-expansive directions) and gate 4 of v6.

## Lesson for general BH

Rigidity is monotone: carving never destroys it. So (SEED) splits cleanly into two parts:
- a rigid ambient SFT over the overgroup;
- a seed carved inside it by local rules.

The known ambient-builders are compression codings and deterministic finite-fibre extensions. Both
are complexity-neutral relative to what they are built on. So a rigid seed over a group with hard word
problem needs a rigid ambient whose own local rules already encode computation, i.e. programmable
rigidity (v6 gate 4) placed at the seed, which is CAP rung 1c. Conversely, any CAP theorem must bound
what **rigid ambients** can carry, since the carving step is free.
