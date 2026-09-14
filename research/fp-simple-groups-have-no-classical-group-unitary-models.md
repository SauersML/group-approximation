---
rg: 2
id: fp-simple-groups-have-no-classical-group-unitary-models
kind: claim
title: A finitely presented infinite simple group has no hyperlinear or sofic approximation through representations or actions of finite classical groups
distinct_from:
  gap-sofic-approximations-are-local-embeddings: that treats sofic approximations through affine maps of finite vector spaces and PGL_m(F_q) on lines, for any countable group; this treats every unitary representation, hence every action, of every finite group whose commutator subgroup is quasi-simple classical, for finitely presented infinite simple groups
  simple-group-width-over-all-finite-simple-groups: that concerns weak soficity through conjugation-invariant lengths on finite simple groups; this concerns hyperlinear and sofic approximations measured by normalized traces
---

**ESTABLISHED (lane sk-fp-sofic-c, 2026-09-13, unreviewed).** Proof: `fp-simple-groups-have-no-classical-group-unitary-models-proof`.

Let `S` be a finitely presented infinite simple group with finite generating set `X`. Let `Q_k` be finite groups whose
commutator subgroups `[Q_k,Q_k]` are finite quasi-simple classical groups: `GL_N(q)`, `SL_N(q)`, and the unitary, symplectic
and orthogonal analogs, in any ranks and over any finite fields. Then there are no:
- maps `φ_k : X → Q_k`, and
- unitary representations `ρ_k` of `Q_k`,

such that `x ↦ (ρ_k(φ_k(x)))_ω` extends to an injective homomorphism `S → ∏_ω (U(d_k), ‖·‖_2)`.

**Consequences.**
- `S` has no sofic approximation through actions of these groups on finite sets. That covers vectors, subspaces, flags,
  cosets of any subgroup, and conjugation actions. This extends `gap-sofic-approximations-are-local-embeddings` from vectors
  and lines to all actions.
- `S` has no hyperlinear approximation through any of their unitary representations, including Weil, cuspidal, Steinberg and
  permutation modules.
- **Ring route.** Composing a rank model into `M_N(F_q)` with any representation of `GL_{nN}(F_q)` never gives hyperlinear
  models of a finitely presented infinite simple `EL_n(R)/Z`. So gate (c) of `sofic-fp-simple-kazhdan-group-from-fp-simple-ring`
  needs finite targets outside these families, at least at the relator images.
- The statement needs no property (T). It covers:
  - the binary Leavitt unit group (hyperlinear half open: `binary-leavitt-unit-group-hyperlinear`);
  - the Caprace–Rémy lattices;
  - the Titz Mite–Witzel kernels, if they are simple.

**Remaining room.**
- Symmetric and alternating targets, whose ratios tend to 1 at elements of small support. This is where sofic permutation
  models of the answered Pestov group live.
- Unbounded direct products of gapped groups.
- Finite groups with long chief series outside these families.
- Unitary models that do not factor through finite groups at all.
