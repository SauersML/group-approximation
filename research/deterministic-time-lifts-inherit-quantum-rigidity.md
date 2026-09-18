---
rg: 2
id: deterministic-time-lifts-inherit-quantum-rigidity
kind: claim
title: An SFT over a product that is deterministic in one factor is quantum rigid whenever its row SFT is, and it is free only if the row SFT is free; over a free space factor such lifts are never free
distinct_from:
  quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products: that turns quantum rigidity into a finitely presented crossed product; this produces quantum rigidity over a product from rigidity of one factor's row SFT, and says what a deterministic coding can and cannot add.
  sft-crossed-product-fp-iff-quantum-rigid: that is the Z^2 equivalence; this is a transfer lemma over any product of finitely generated groups.
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that defines the operator conditions Q1-Q3 used here; this proves a permanence property of them.
---

**ESTABLISHED** by the proof below (lane bh-free-25, gate G2 second angle, 2026-09-18;
elementary, not reviewed). Quantum rigidity (conditions Q1–Q3) is as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Setting

- `Λ = Λ_1 × Λ_2`, with finite generating sets `S_1, S_2` and the word metric of
  `S_1 ∪ S_2`.
- `Y ⊆ A^{Λ_2}` is an SFT that is `D`-quantum rigid over a field `k`.
- `Φ: Λ_1 → Aut(Y)` is an action by shift-commuting homeomorphisms, that is, invertible
  cellular automata of `Y`. For `s ∈ S_1`, `Φ_s` and `Φ_s^{-1}` have local rules
  `φ_s`, `ψ_s` of radius `R`.
- The **lift** `X ⊆ A^Λ` is the set of `x` whose rows `x(g,·)` lie in `Y` and which satisfy
  `x(gs, h) = φ_s(x(g, hB_R))` and `x(g, h) = ψ_s(x(gs, hB_R))`. These are local rules, so
  `X` is an SFT.
- Every SFT over `Λ` that is deterministic in both directions of every `s ∈ S_1`, and whose
  row projection is an SFT, is such a lift. This includes automaton and self-similar
  space-time codings in which `Λ_1` plays time.

## Statement

1. `x ↦ x(1,·)` conjugates `(X, Λ)` to `Y` with the joint action `(g, λ)·y = Φ_g(σ_λ y)`.
2. `X` is `D'`-quantum rigid for `D' = max(D, R + 1)`.
3. `X` is free (resp. minimal) exactly when the joint action on `Y` is. In particular, `X`
   free forces `Λ_2` to act freely on `Y`.
4. If `Λ_2` is a free group `F_n`, then no lift is free. The reason is Piantadosi's
   theorem, cited as usually quoted and not re-read: every nonempty SFT over `F_n` has a
   point with finite orbit.
5. Linear lifts over a free space factor are trivial. An invertible linear cellular
   automaton of `F_p^{F_n}` is a unit of `F_p[F_n]`. Units there are trivial (free groups
   are orderable, Higman), so the automaton is a scalar times a shift.

## Proof

1. The rows are determined by row `1` through `Φ`, and every `y ∈ Y` extends. The shift by
   `(g, λ)` corresponds to `Φ_g ∘ σ_λ`.
2. Let `E_a(g, h)` satisfy Q1–Q3 for `X` at `D'`.
   - *Each row commutes.* For fixed `g`, the family `(E_a(g, h))_h` satisfies Q1–Q3 for `Y`
     at `D`. Row sites at `Λ_2`-distance `≤ 2D` are at `Λ`-distance `≤ 2D ≤ 2D'`, and the
     patterns forbidden in `Y` are forbidden in `X`. By rigidity of `Y` the row family
     commutes. Call the algebra it generates `C_g`.
   - *Neighbouring rows are polynomials in each other.* Sites `(gs, h)` and `(g, h')` with
     `h' ∈ hB_R` are at distance `≤ R + 1 ≤ 2D'`, so they commute (Q2).
     - Q3 kills `E_a(gs, h)·∏_{h'} E_{π(h')}(g, h')` whenever `a ≠ φ_s(π)`.
     - Multiply the two partitions of unity, which commute. This gives
       `E_a(gs, h) = Σ_{π: φ_s(π) = a} ∏_{h' ∈ hB_R} E_{π(h')}(g, h')`, so `C_{gs} ⊆ C_g`.
     - The `ψ_s` rule gives `C_g ⊆ C_{gs}` in the same way.
   - *Conclusion.* So `C_g = C_{gs}` for all `g` and `s`. All `E` lie in the commutative
     algebra `C_1`, so they commute.
3. Immediate from 1.
4. A point `y` with finite `Λ_2`-orbit has a nontrivial stabilizer `λ`. Then `(1, λ)` fixes
   the corresponding point of `X`.
5. By Curtis–Hedlund the inverse of a linear bijective cellular automaton is again a linear
   cellular automaton. Composition is multiplication in `F_p[F_n]`. ∎

## Lesson for general BH

- **Deterministic directions are free for rigidity, and they add none.**
  - In a lift, every wall perpendicular to the time factor is automatically rigid, since
    one row determines everything.
  - Rigidity against walls in the space factor comes from rigidity of the row SFT, or from
    the time action carrying information across space walls.
- So for gate G2 over `Λ_1 × Λ_2`, a time-deterministic coding (automaton, self-similar or
  space-time) reduces the crux to a Λ_2-free, quantum-rigid row SFT `Y` over `Λ_2` whose
  automorphism group contains a copy of `Λ_1` acting jointly freely and minimally.
  Minimality may come entirely from `Λ_1`.
- **Consequences for the `F_2 × F_2` target.**
  - The space factor cannot be free (item 4).
  - Ledrappier's mechanism, permutive linear time carrying information across space walls,
    has no invertible linear version over a tree (item 5).
  - A non-invertible time rule over a free time group branches backward. That suggests
    independent choices on both sides of time walls; it is not proved here.
- **Design rule this suggests (not proved).** Over `F_2 × F_2`, a rigid coding should be
  genuinely coupled: deterministic in neither factor alone. Otherwise, over a
  one-ended-by-surface product `Λ_0 × F_2`, take `Λ_1 = F_2` as time and `Λ_2 = Λ_0` as
  space. `Λ_0` must then carry a strongly aperiodic, quantum-rigid SFT with a free `F_2`
  of automorphisms.
