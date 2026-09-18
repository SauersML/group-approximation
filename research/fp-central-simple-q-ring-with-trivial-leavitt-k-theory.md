---
rg: 2
id: fp-central-simple-q-ring-with-trivial-leavitt-k-theory
kind: claim
title: Some finitely presented ring is a simple Q-algebra with centre Q whose Leavitt tensor B ⊗ L_Q(1,2) has K_1 = K_2 = 0
distinct_from:
  algebra-boone-higman-conjecture: that asks to embed every decidable finitely generated algebra in a finitely presented simple algebra; this asks for one finitely presented simple ring of characteristic zero, with a K-theory side condition.
  infinite-field-leavitt-units-are-not-finitely-generated: that shows no finitely generated subring of a Leavitt algebra over a field contains Q; this asks for a finitely presented ring that does, which must therefore be noncommutative and not of that form.
  q-embeds-in-a-corner-of-a-fp-toeplitz-ring: that is a finitely presented ring containing Q in a corner, which is not simple; this asks for a simple one with Q as the centre.
---

**OPEN.** There is a unital ring `B`, finitely presented as a ring, such that:
- `B` is simple;
- `B` contains `Q`, so it is a `Q`-algebra of characteristic zero;
- the centre of `B` is `Q`;
- `K_1(B ⊗_Q L_Q(1,2)) = K_2(B ⊗_Q L_Q(1,2)) = 0`, which holds for instance when `B`
  is regular supercoherent (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).

**Why.** With `q-coefficient-leavitt-tensor-unit-groups-are-fp`, such a `B` gives a
finitely presented group `(B ⊗ L_Q(1,2))^x` containing `GL_∞(Q)`. So an explicit `B`
answers `gl-n-q-explicit-natural-fp-overgroup` (route
`gl-n-q-explicit-via-q-coefficient-leavitt-tensor-host`). It does not by itself give a
finitely presented *simple* host: the scalar quotient by `Q^x` is not finitely presented
(the scalar obstruction in that claim).

**Constraints.**
- `B` must be noncommutative. A finitely generated commutative ring containing `Q`
  does not exist: reducing modulo a maximal ideal over a prime that is not a unit gives
  a contradiction.
- `B` is not a finitely generated subring of any Leavitt algebra over a field
  (`infinite-field-leavitt-units-are-not-finitely-generated`, part 3).
- The nearest landed object is the finitely presented Toeplitz ring of
  `q-embeds-in-a-corner-of-a-fp-toeplitz-ring`. It contains `Q` in a corner but has
  proper ideals, so the division and GE inputs of the Leavitt tensor argument fail for it.
- Existence of any finitely presented simple ring of characteristic zero is the
  characteristic-zero part of the algebra Boone–Higman question. Evans–Mandelberg–Neff
  treat characteristic `p`.
