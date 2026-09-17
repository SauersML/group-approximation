---
rg: 2
id: compressible-base-controlled-automata-are-strict
kind: claim
title: Over a compressible Cantor base, point-controlled automata are strict, so a surjunctivity proof for V must use that the rule is constant along the Cantor coordinate
distinct_from:
  full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant: that shows the full shift cannot be encoded into coset shifts over Cantor orbits; this keeps the full shift and lets the local rule read the Cantor point, and shows strictness then comes for free.
  thompson-v-cantor-system-has-no-covariant-rank-model: that excludes covariant rank models of the cylinder algebra; this is the automaton-level statement that every argument valid over the transformation groupoid of the Cantor action proves a false statement.
  thompson-v-coset-stabilizers-contain-copies-of-v: that kills coset peeling because stabilizers contain copies of V; this is a class obstruction for every fibrewise-over-the-Cantor-set argument, independent of stabilizers.
artifacts:
  - research/compressible-base-controlled-automata-are-strict-proof.md
---

**ESTABLISHED (obstruction; proof in the artifact).**

**Setting.** Let a group `G` act on a compact zero-dimensional space `X`, and let
`A` be a finite alphabet, with `G` acting on `A^G` by `(g.y)(h) = y(g^-1 h)`.
An *`X`-controlled automaton* is a continuous map
`Phi : A^G x X -> A^G x X` of the form `Phi(y, x) = (tau_x(y), x)` with:
- `Phi(g.y, g.x) = g.Phi(y, x)` for all `g`;
- `tau_x(y)(e)` a function of `y|_S` and of the cell of `x` in a finite clopen
  partition of `X`, for a finite set `S` in `G`.

An ordinary automaton is the case where `tau_x` does not depend on `x`.

Call `X` *compressible* if there are a clopen partition `X = U_1 ⊔ ... ⊔ U_n`
and elements `s_1, ..., s_n` in `G` such that `T(z) = s_i z` on `U_i` is
injective and `T(X) != X`.

**Theorem.**
1. If `X` is compressible and `|A| >= 2`, there is an injective, non-surjective
   `X`-controlled automaton with `S = {s_1, ..., s_n}`. If the action is minimal,
   it is non-surjective on every fibre `A^G x {x}`.
2. Thompson's `V` on `C = {0,1}^N` is compressible, with `n = 2` and `T(z) = 0z`.
   So is `F_2` on its boundary.
3. **Calibration.** If `G` is amenable and `X` is minimal, every injective
   `X`-controlled automaton is surjective (relative variational principle; sketch
   in the artifact).

**What this kills.** A proof of `thompson-v-surjunctive` cannot use an automaton
only through its restrictions to Cantor pieces. That includes:
- induction on clopens using `V_U ~= V`;
- germ-by-germ peeling along orbits;
- groupoid-level transfers through `C x| V`;
- Radon–Nikodym-weighted counting against quasi-invariant measures on `C`.

Any such argument also applies to `X`-controlled automata over `C`, and part 1
refutes the result there.

The exact failing step is the one where the argument passes from "the rule is
the same at every site" to "the rule is determined, site by site, by the Cantor
germ at that site". After that step the hypothesis no longer excludes the
compression swindle `T(z) = 0z`.

Part 2 for `F_2`, together with the Gromov–Weiss theorem for sofic groups, shows
that controlled strictness does not imply ordinary strictness. So this
obstruction constrains proofs; it does not refute the claim. The rule's
independence from the Cantor point is exactly what a successful argument must
spend. It is not stabilizer-commutation: `tau_x` commutes with
`Stab(x)` automatically. It is the relation `tau_x = tau_(gx)` for elements `g`
that move `x`, which the swindle breaks at the boundary of `T(C)`.
