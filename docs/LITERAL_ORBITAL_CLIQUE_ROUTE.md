# The orbital graph is a disjoint union of complete blocks

Date: 2026-08-16.  Status: **one direction proved, one direction open**, with
the open direction specified here to the level of named lemmas.  Nothing in
this document is asserted as established.

This is the last mathematical gap between the literal group's normal form and
the soficity tower.  It is written down because it was repeatedly mistaken for
a formalization task when it is a theorem nobody has proved, in Lean or on
paper, and because a previous attempt to write it produced a module whose
proofs referenced six lemmas that do not exist.

## Statement

In `GroupApproximation/Sofic/LiteralBlockNormalForm.lean`:

```text
Adjacent ξ η  ↔  blockOf ξ = blockOf η  ∧  ξ ≠ η
```

* `Site = Vertical ⧸ baseSubgroup`, `Block = Vertical ⧸ blockSubgroup`,
  `blockSubgroup = baseSubgroup ⊔ ⟨β⟩` with `β = t⁻¹ v₁ t`.
* `Adjacent ξ η` is the orbital relation: the ordered pair, in one of its two
  orders, is a `Vertical`-translate of the marked pair `(τo, v₁τo)`.

## Direction proved (`→`), landed 2026-08-16

`blockOf_eq_of_adjacent`, with `blockOf_smul` and `blockOf_siteA`.  The marked
pair shares a block because `β ∈ blockSubgroup` is what that subgroup was
defined for; the edge relation is a translate; `blockOf` is equivariant.
Contrapositive `not_adjacent_of_blockOf_ne` is recorded beside it: lamps at
sites of different blocks commute outright rather than through the sign.

## Direction open (`←`)

Two distinct sites of a common block are a translate of the marked pair.
Equivalently: the block subgroup acts **two-transitively** on the eight sites
of a block.

### Why eight, and why two-transitive

`K/B` is the parity group `(ℤ/2)³`.  The doubling relation `t vᵢ t⁻¹ = vᵢ²`
puts every square of a translation into the base, so only the exponent vector
modulo two survives; `LiteralBaseDoublingIndex.exists_parity_coset` and
`finite_quotient_doubledBase` are that statement at the level of the base.  So
a block carries eight sites indexed by `(ℤ/2)³`, and the marked pair is the
parity pair `(0, e₁)`.

Two-transitivity of the affine group on `(ℤ/2)³` factors into two inputs, both
of which already exist in some form:

1. **Translations are simply transitive on the eight parities.**  Moves any
   site of a block to any other.  Follows from the coset description; needs
   the parity coordinates transported from `Base` to `Vertical`.
2. **Rotations are transitive on the seven nonzero parities.**  The six words
   `x, x², z, yz, yx, y²x` do it.  This is *already used* — it is the same
   fact `Sofic/LiteralSignFreeQuotient.lean` uses to reduce every parity
   commutator to a conjugate of the mark, validated numerically over
   `GL₃(𝔽₂)` before transcription.

Given both, translate the first site onto `τo`; the second lands on a site of
the marked block distinct from `τo`, so its parity is nonzero; a rotation word
carries that parity to `e₁` while fixing `τo`.  The composite carries `(ξ, η)`
to the marked pair.

### What has to be built first

The parity apparatus lives at the `Base` level and the blocks live at the
`Vertical` level, so the transport is the real work, not the transitivity:

* `parityOf : Site → (ZMod 2 × ZMod 2 × ZMod 2)` on the sites of a fixed
  block, well defined because squares of translations lie in the base;
* `parityOf` is a bijection from the sites of one block onto `(ℤ/2)³`;
* the rotation-word transitivity of `LiteralSignFreeQuotient`, restated
  against `parityOf` rather than against conjugates of the moved lamp.

None of these exist.  A module claiming the biconditional without them is
claiming the theorem.

## What it unlocks, in order

1. `LampFactor ≃* BlockCliffordIndex.BlockCliffordI Block Fib` — the lamp
   relations braid along `Adjacent`, the block relations along equality of
   blocks, so the biconditional is exactly what identifies the two
   presentations.  `Sofic/BlockCliffordIndex.lean` supplies the arbitrary-index
   target, since the literal block set is infinite.
2. Together with an identification of `Vertical` with the mapping telescope by
   `ℤ` — a second completeness theorem, also unproved — the soficity tower of
   `Sofic/BlockCliffordTowerSofic.lean` applies to the model.
3. `markedGroup_isSofic`, and with it a finitely presented sofic non-MF group,
   strengthening `thm:E` from the finitely generated witness to the source.

Until step 1, the manuscript's statement that soficity of `E` is open is
correct, and it should not be edited.
