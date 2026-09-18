---
rg: 2
id: topologically-free-subshift-full-groups-force-quantum-rigidity
kind: claim
title: The necessity theorem holds for topologically free actions, so a finitely presented V-stabilized full group forces quantum rigidity and finite type of any topologically free subshift
requires: [fp-v-times-subshift-full-groups-force-quantum-rigidity]
distinct_from:
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that assumes the acting group acts freely on the subshift; this weakens freeness to topological freeness, which is the form in which boundary actions of lattices (periodic flats, loxodromic fixed points) satisfy it.
  v-times-quantum-rigid-sft-full-groups-are-fp: that is the open converse (rigidity implies finite presentation); this is the necessity direction for a larger class of actions.
---

**ESTABLISHED** (lane proof, elementary; bh-invent-12, 2026-09-18; not independently reviewed; no
priority claimed).

## Statement

Let `Λ` be finitely generated, `X ⊆ A^Λ` a subshift, `T = G_V × (Λ ⋉ X)`, and `t_s`, `e_a` as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`. Assume only that `Λ` acts
**topologically freely** on `X`: for `g ≠ 1`, `Fix_X(g)` has empty interior.

Then parts 1 and 2 of that theorem hold verbatim. If a finitely presented `Γ ≤ F(T)` contains every
`t_s` and `e_a`, then `X` is `D`-quantum rigid over every field for all large `D`. If also
`V × {1} ≤ Γ`, then `X` is of finite type. In particular, if `F(T)` is finitely presented, `X` is a
quantum rigid SFT.

## Proof

The route `fp-v-times-subshift-full-groups-force-quantum-rigidity-proof` uses freeness at exactly one
point: injectivity of `β_(x') : C_0 × Λ -> C × X`, `(c, z) -> (c, z.x')`. That route says so itself:
"Lemma R uses neither minimality nor finite type, only freeness". The map is injective as soon as the
stabilizer of the single point `x'` is trivial.

- **Where `x'` is chosen.** In Lemma R, `x'` is any point of `X` realizing a given occurring pattern
  `α` on the window `z^(-1) B_D`. In Part 2, `x'` is any point of `X` agreeing with `y` on a window
  where `y` agrees with some point of `X`. In both places the admissible `x'` form a **nonempty open**
  subset of `X`, a cylinder of an occurring pattern.
- **Free points are dense.** `Λ` is countable. Each `Fix_X(g)`, `g ≠ 1`, is closed with empty
  interior, so the points with trivial stabilizer form a dense `G_δ` (Baire). Every nonempty open set
  contains one.
- **The fix.** Choose `x'` with trivial stabilizer in the admissible cylinder. The rest of each
  argument uses only that `x'` realizes the pattern: `E_a(q) P_α = [x'(q) = a] P_α` on the window, and
  `ψ_(x')(w)` is the transported action. So it runs unchanged.

Part 1 (the commutator `[g_1, g_2]`), Section 4 (monotonicity and metric independence) and the
Corollary `F(T) = A(T)` never use freeness. `∎`

**Calibration.**
- For free actions every point is free, and the statement is the original one.
- The hypothesis cannot be dropped entirely. If some `g ≠ 1` fixes a cylinder `U` pointwise, then
  `t_g` acts on `C × U` as the identity, and relators of `Γ` no longer see the sites of `U`.

## Lesson for general BH

The necessity theorem ("finitely presented V-stabilized full group implies quantum rigidity") is
really about **generic points**. Freeness enters only through one representation of `Λ` on an orbit,
and a single free orbit per cylinder suffices. So every finitely presented full-group host whose
groupoid is (a reduction of) `G_V × (Λ ⋉ X)`, with `Λ ↷ X` merely topologically free, certifies
quantum rigidity of `X`. Boundary actions of lattices are the main source of such hosts
(`a2-lattice-boundary-skew-shifts-are-quantum-rigid`).
