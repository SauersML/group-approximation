---
rg: 2
id: z2-o2-phantom-tensor-square-is-sai-and-self-dual
kind: claim
title: A Z/2-phantom is square-zero iff its diagonal crossed product is contractible iff its Takai dual is square-zero; on O_2 the square action is strongly approximately inner, and square-zero means a Rokhlin square
distinct_from:
  zp-restriction-trivial-splits-cellular-plus-phantom: that proves a phantom's tensor square has θ = 1 and is a retract of a trivial-action algebra; this adds Takai self-duality of square-zero-ness, the dynamical O_2 forms, and the calibration that Rokhlin squares need not descend to factors.
  o2-contractible-crossed-product-inner-half-flip-mcduff: that proves approximately G-inner half-flip and Rokhlin infinite tensor powers; this is about vanishing of the finite tensor square.
---

**ESTABLISHED (derivation; unreviewed).**
- `G = Z/2`.
- A *phantom* is a separable `G`-algebra `D` with `Res D ≃_KK 0` and `D ⋊ G ≃_KK 0`.
- A phantom is *square-zero* if `D ⊗ D ≃_(KK^G) 0`, with the minimal tensor product and the diagonal
  action.

1. **Categorical.** For a phantom `D`, `D ⊗ D ≃ 0` iff `(D ⊗ D) ⋊ G ≃_KK 0`.
2. **Takai self-duality.** `D̂ = D ⋊ G`, with the dual action, is a phantom, and
   `(D ⊗ D) ⋊_(α⊗α) G` is Morita equivalent to `(D̂ ⊗ D̂) ⋊ Ĝ`. So `D` is square-zero iff `D̂` is.
3. **On `O_2`.** Let `α : G ↷ O_2` be pointwise outer with `O_2 ⋊_α G ≃_KK 0`.
   - (a) `α ⊗ α` is strongly approximately inner. It is implemented by invariant averages of
     `w_n ⊗ w_n`, where `w_n` are the anti-invariant implementing unitaries from item 2(a) of
     `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`.
   - (b) The following are equivalent:
     - `(O_2, α)^(⊗2) ≃_(KK^G) 0`;
     - `α ⊗ α` has the Rokhlin property;
     - `(O_2 ⊗ O_2) ⋊_(α⊗α) G ≅ O_2`;
     - `2[1] = 0` in `K_0(F^(α⊗α))`;
     - `O_3` embeds unitally into `F^(α⊗α)`.
4. **Calibration.** For every pointwise outer `α : G ↷ O_2`, `α ⊗ id_(O_2)` has the Rokhlin
   property. So the Rokhlin property does not descend from a tensor product to a factor.

**Reading.**
- Square-zero-ness of a phantom is a non-equivariant KK statement about one crossed product, and it is
  invariant under Takai duality.
- On `O_2` it is the Rokhlin property of the square action, which is always strongly approximately
  inner.
- Whether a nonzero phantom can be square-zero is the open `z2-o2-phantoms-are-not-square-zero`.

**Model tests.**
- The trivial action on `O_2` is not outer. Its square is KK^G-contractible but not Rokhlin.
- An inner symmetry `Ad(s)` is not outer. Its square `Ad(s ⊗ s)` is strongly approximately inner but
  not Rokhlin.
- So outerness is needed in 3(b) and in 4.
- The Rokhlin model is the zero object and satisfies every item.

**Standard inputs (not re-read):**
- the Kasparov external product;
- Takai duality, and Green–Takai subgroup duality for finite abelian groups;
- crossed products commute with exterior tensor products;
- `α ⊗ β` is outer on simple algebras whenever `α` is outer;
- Kirchberg–Phillips for KK-contractible unital Kirchberg algebras.

**Review status of the O_2 inputs.** `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` and
`z2-odd-commutator-below-half-forces-commuting-towers` passed ex-verify2-analysis in its O_2 census
(`research/artifacts/ex-review2-analysis-2026-09-13-part15.md`, d5b493c4bc). This node is unreviewed.

Artifact: `research/artifacts/uct-z2-square-zero-phantoms-2026-09-13.md` §2.

Proof: `z2-o2-phantom-tensor-square-is-sai-and-self-dual-proof`.
