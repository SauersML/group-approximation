---
rg: 2
id: z3-equivariant-permutations-are-stably-realizable
kind: claim
title: Every Z_3-equivariant permutation of {0,1}^3, extended by one identity ancilla track, is the shadow of an equivariant polynomial automorphism
distinct_from:
  z3-weight-one-rotation-is-not-an-automorphism-shadow: that asks about one track, where the weight-one rotation is still undecided; this adds one identity ancilla track, where every equivariant permutation, the weight-one rotation included, is realized.
  structurally-reversible-automata-are-formalizable: that proves words of track shears are formalizable on every group; this realizes a level-dependent rotation through commutators of line-controlled level flips with level-controlled SL_2(F_4) shears.
artifacts:
  - research/artifacts/z3-rotation-stable-realization-2026-09-12.md
---

Let `R` act diagonally on two tracks `A^3 x A^3` over `F_2`. For every permutation `psi` of
`{0,1}^(Z_3)` that commutes with the shift, there is an `R`-equivariant polynomial automorphism of
`A^6` over `F_2` whose Boolean shadow is `psi x id`.

**Consequences.**
- **Stable formalizability.** By `finite-group-formalizability-equals-equivariant-automorphism`
  (stable form), every bijective pair on `{0,1}^(Z_3)` is stably formalizable with one ancilla
  track. In particular this holds for the weight-one rotation `rho` and for the order-three control
  of `own-block-local-bijection-rows-peel`.
- **One-track rigidity does not stabilize.** Whether `rho` is a one-track shadow is undecided, but that
  question cannot witness against `injective-binary-automata-are-stably-formalizable`.

**The construction** (artifact Sections 1–2).
- **Moves:** the diagonal shift; shears `v_1 -> v_1 + s_1 c v_2` and `v_2 -> v_2 + s_1 c v_1` with
  `c in F_2[R] = F_4`; and flips `s_1 -> s_1 + p(v_1, v_2)` with `p` invariant.
- **Lemma 1:** commuting a flip controlled by the line `l` with the level-controlled shear word of
  `A in SL_2(F_4)`, where `A l = l` and `A|_l = omega`, rotates `l` by `omega^2` at `s_1 = 1` and by
  `omega` at `s_1 = 0`.
- **Theorem 2:** multiplying these commutators over the five lines, composing with the diagonal shift
  and with the level-controlled `diag(omega^2, omega)` gives `(u_1, u_2) -> (omega^(s_1) u_1, u_2)`,
  which is `rho x id`.
- **Corollary 3:** the uniform-shadow group `K` is maximal in the order-36 group, so `K` and `rho`
  generate every equivariant permutation.

**ESTABLISHED 2026-09-12** by `z3-equivariant-permutations-stably-realizable-proof`. Verification
requested from w3-vf-nonlinear.
