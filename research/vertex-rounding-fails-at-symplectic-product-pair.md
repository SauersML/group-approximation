---
rg: 2
id: vertex-rounding-fails-at-symplectic-product-pair
kind: claim
title: Vertex rounding fails at a trace-preserving model of the product of the affine symplectic group with the Theorem E pair
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1) at every model of every infranormal, non-normal Kazhdan pair; this is one explicit pair and one explicit model at which (H1) fails, which refutes that general form.
  rf-kazhdan-group-not-flexibly-hs-stable: that gives non-roundable asymptotic representations of the affine symplectic group alone, with no ambient group; this extends amplified copies of them to a trace-preserving model of an infranormal Kazhdan actor and proves non-roundability at every generating set of the vertex.
  fournier-facio-vertex-rounding-fails-at-every-model: that shows rounding fails at every faithful model of the Fournier--Facio pair, whose existence needs hyperlinearity of that group; this works at a residually finite actor with an explicit model, so it needs no hyperlinearity input.
  leavitt-pair-vertex-rounding-is-nonhyperlinearity: that ties (H1) at the nine-leaf Leavitt pair to non-hyperlinearity of the unit group; this refutes the general form unconditionally at a different pair.
  layered-weil-actor-models-non-roundable-and-normalizing: that is a non-roundable vertex model at an ascending HNN actor, which is not Kazhdan; this is at an actor with property (T), as the general claim requires.
  kt-actor-model-with-totally-non-roundable-vertex: that asks for a non-roundable actor model at the Theorem E pair itself; this puts the non-roundable part on an added affine symplectic direct factor and says nothing about the Theorem E vertex.
artifacts:
  - research/artifacts/vertex-rounding-product-pair-2026-09-16.md
---

**ESTABLISHED (unreviewed).** Let `g >= 2`, `q` a prime power and `r, d >= 3`. Put
`Γ_g = Z^(2g) ⋊ Sp_(2g)(Z)` and let `K = EL_r(F_q[x_1..x_d]) < H = EL_r(F_q[x_1^(±1)..x_d^(±1)]) ⋊ SL_d(Z)` be
the Kun--Thom Theorem E pair. Put

```text
Γ = Γ_g × K   <   G = Γ_g × H.
```

1. **The pair.** `Γ` and `G` are residually finite Kazhdan groups, and `Γ` is infranormal but not normal in
   `G`. The compression semigroup is `Γ_g × P_K`.
2. **The model.** There are a nonprincipal ultrafilter `U` and a trace-preserving homomorphism
   `σ : G -> U(prod_U M_n)` whose coordinates, on a set `D = {N_j} ∈ U`, are
   `σ_(N_j)(a, h) = α_(k_j)(a) ⊗ λ_j(h)`. Here `α_k` are the projective Heisenberg models of
   `rf-kazhdan-group-not-flexibly-hs-stable`, with `k_j -> ∞`, and `λ_j` are permutation representations of
   `H` on the finite quotients of a residual chain. For a nonprincipal `U` fixed in advance, amplifying these
   coordinates and padding by `o(n)` gives a trace-preserving model on `prod_U M_n` with the same obstruction
   (artifact, Remark 6.3).
3. **No rounding.** For every finite generating set `F` of `Γ`, and so for every Kazhdan pair `(F, κ)`, there
   are no genuine `π_n` rounding `σ_n|Γ` on `F`. This holds both after `o(n)` padding on both sides, and in
   Dogon's compression form (arXiv:2211.10492, Definition 1.2).

So the general form of `hs-stable-vertex-rounding-for-every-model` is false.

Derivation: `vertex-rounding-fails-at-symplectic-product-pair-proof`. Full proof in the artifact.

**Reading.**
- **Why it works.** The vertex contains a Kazhdan direct factor, `Γ_g`, whose Heisenberg cover `Γ~_g` is
  Kazhdan. A rounding of the amplified models `α_k ⊗ 1_m` makes a bimodule vector almost invariant under
  `Γ~_g`, while the centre acts by `e^(2πi/k) ≠ 1`. The Kazhdan constants do not depend on `m`, so
  amplification does not help. The `H` factor makes the pair infranormal and the model trace-preserving.
- **What it does not decide.** (H1) at the Theorem E pair itself, now
  `theorem-e-vertex-rounds-at-every-actor-model`. There `H_2(K; Z) = 0` in the stable range `r >= d + 3` (van der Kallen and Quillen
  imports, not source-verified), so scalar
  cocycle models of `K` round strictly (`finite-multiplier-projective-models-round-strictly`). Also
  `kt-centralizer-normalization-hs` at this model.
- **Lesson.** A true general rounding statement must restrict the vertex beyond (T), residual finiteness and
  infranormality. Any Kazhdan direct factor with amplification-robust non-roundable trace-preserving models
  breaks it.
