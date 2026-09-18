# G2(c) lane bh-g2-f2f2: coset shifts, pair types and the rigidity–freeness trade-off (2026-09-18)

This lane worked gate G2(c) of `gq-bh-synthesis-master-route.md`: a quantum-rigid free minimal SFT over
F₂×F₂ (or Λ₀×F₂). The object was not found. The lane found a general mechanism, the two ways it
fails, and what a working design must do. All results are lane proofs, elementary and unreviewed,
with no priority claimed.

## 1. The mechanism: pair types

For a subshift X ⊆ A^Λ of right-Δ-invariant configurations (a *coset shift*, X ≅ Z ⊆ A^{Λ/Δ}):

- **Local Δ-invariance lifts to operators.** Every D-quantum family satisfies E(λδ) = E(λ). So it lives
  on Λ/Δ.
- **Short types commute for free.** Two points of Λ/Δ whose double coset Δλ⁻¹λ'Δ has a representative of
  length ≤ 2D have commuting families, however far apart the points are.
- **Descent.** Any other pair commutes if one point is a function of finitely many nearby points, and
  each of those forms a pair of smaller complexity with the other point.

Node: `coset-invariant-sft-rigidity-descends-along-double-cosets`, with proof
`coset-invariant-sft-rigidity-descent-proof`. With Δ = 1 it is the operator form of the
permutive-triangle and Ledrappier arguments.

## 2. Extreme 1: finitely many pair types (Cornulier regime)

**Result.** If Δ\Λ/Δ is finite, every coset shift is quantum rigid. Over a finitely presented Λ its
crossed product is then finitely presented. This is the algebra twin of Cornulier's criterion for
permutational wreath products. Node: `cornulier-regime-coset-sfts-are-quantum-rigid`.

**The cost.** Every such action on main (V, F, T, CT_P(Z), highly transitive and order-transitive
actions) has property (IS): any finite set can be moved into any infinite set. Under (IS), every closed
invariant set contains a constant configuration. So there is no free subsystem and no infinite minimal
one. Node: `set-transitive-coset-shifts-have-only-constant-minimal-sets`.

**The shortcut left open.** A finite double-coset space *without* (IS) that carries a free minimal
coset SFT would be rigid for free. Node: `finite-double-coset-space-with-free-minimal-coset-sft`.

## 3. Extreme 2: stabilizers that rotate determinism (two-sided F₂)

Take Λ = F₂×F₂ acting on F₂ by (p,q)·k = pkq⁻¹, with Δ the diagonal.

- **Pair types** are the conjugacy classes of F₂. Everything conjugate to a short element commutes for
  free.
- **Descent works.** Any local determinism giving cyclic-length descent, for example determinism
  behind a feedback set of de Bruijn directions, would make the coset SFT quantum rigid.
- **But the subshift collapses.** Two-sided invariance puts every rule into every frame kr⁻¹Sr.
  Cyclic descent is decided by bounded local contexts, so it also occurs inside every long linear word.
  Inserting the rule at that cut through the frame r = Q shortens the word. So a ball determines the
  next ball, and Z is finite. Node: `two-sided-free-group-coset-sfts-collapse-under-cyclic-descent`.
- **Walls are automatic.** Vertical and horizontal walls of the product of trees determine everything,
  so the classical wall kills never apply.

## 4. What a working design must do (the lesson)

Rigidity costs symmetry twice:
- **Pair types.** Large point stabilizers merge pair types, which is what gives free commutation.
- **Rotation.** The same stabilizers rotate determinism rules into all frames, which gives collapse.
- **Homogeneity.** Taken to the limit, symmetry is homogeneity (IS), which gives constant points.

Rigid infinite shifts known today, Ledrappier and the permutive triangles, are rigid because their
determinism is **directional**: rows determine what lies above them, never a ball determining
everything.

**Design target.** Point stabilizers large enough to merge pair types, but fixing a direction (an end,
or a horofunction) along which determinism runs one way. Candidates for a successor:
- coset spaces of F₂×F₂ by cyclic or parabolic subgroups of the diagonal, such as ⟨(a,a)⟩;
- horocyclic codings of products of trees;
- the Mozes-type tilings of lane bh-g2-buildings.

Target node, OPEN with this record as Attempt 1: `f2-times-f2-has-a-quantum-rigid-free-minimal-sft`.
