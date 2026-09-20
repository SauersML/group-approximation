---
rg: 2
id: two-sided-locality-holds-for-matrix-linear-automata
kind: claim
title: Ryan-type theorems do not forbid the commuting pair; left and right multiplication by Laurent polynomial matrices over M_2(F_2) are commuting groups of cellular automata, each containing F_2, acting regularly on growing towers of periodic configurations; but every group of linear automata over a finite ring is exact, so this solves two-sided locality for T1 and never for T2; and hierarchy-level-bounded transports collapse, so transports must be seam-sensitive
requires:
  - loop-labels-reduce-t2-to-two-sided-locality
  - profinite-skew-layers-collapse-into-the-equicontinuous-factor
  - commutator-squeeze-bounds-lifted-lie-translations
distinct_from:
  loop-labels-reduce-t2-to-two-sided-locality: that reduces minimal loop-label designs to a commuting pair of local actions; this constructs such a pair, proves that the construction only ever lifts exact groups, and proves which transports collapse.
  profinite-skew-layers-collapse-into-the-equicontinuous-factor: that proves profinite layers directly over the MEF collapse; this applies the same theorem to transports that are continuous over the skeleton's odometer, and locates the escape in transports that are continuous only over the skeleton.
---

**Status.**
- Items 1–4(a) are ESTABLISHED (lane bh-invent-16, 2026-09-19; elementary; no priority claimed).
- Referee bh-ref-d (6e0fb29940): PASS with three one-line fixes, applied by bh-ra-t2 as the (RA_free) owner:
  - 2-transitivity needs at least 3 points;
  - the inverse step is argued through `R_x(δ_0 · 1)` and continuity;
  - 4(a)'s last line goes through the dense set of all-closed-path points.

  `End(R)` means the additive endomorphism ring `End_Z(R, +)`, a finite ring.
- Items 4(b)–(d) are design statements, not proved.
- The recalled inputs are:
  - Salo's finitary Ryan theorem (arXiv:1610.05487, abstract read);
  - the Tits alternative;
  - free subgroups of `SL_2(F_2[t])` (Nagao's amalgam, recalled);
  - exactness of linear groups (Guentner–Higson–Weinberger).

## Statement

1. **Ryan does not rule out the pair.**
   - Ryan's theorem says the center of `Aut(B^Z)` is the shift group. Salo's finitary version gives a
     finitely generated subgroup whose centralizer is `Z`, and a finitely generated subgroup acting
     transitively of all orders on finite points.
   - These constrain particular subgroups, not every pair one might choose. Commuting non-abelian pairs
     exist, for instance on independent tracks.
   - The relative that bites: **a 2-transitive permutation group on at least 3 points has trivial
     centralizer** (`S_2` shows the bound is needed). So the
     transport group must be far from highly transitive, of regular type, as in the next item.
2. **The pair.** Take the alphabet `R = M_2(F_2)`. For `u = Σ_j a_j t^j` in `M_2(F_2)[t, t^(-1)]` put:
   - `(L_u x)_k = Σ_j a_j x_(k−j)` (left multiplication);
   - `(R_u x)_k = Σ_j x_(k−j) a_j` (right multiplication).

   Then:
   - (a) both are cellular automata on `R^Z`, invertible exactly for units `u`, with `L_u L_v = L_(uv)`,
     `R_u R_v = R_(vu)`, and **`L_u R_v = R_v L_u`**;
   - (b) the unit group `U = GL_2(F_2[t, t^(-1)])` contains a non-abelian free group `F`;
   - (c) the period-`ℓ` configurations form the ring `A_ℓ = M_2(F_2)[t]/(t^ℓ − 1)`. Let `O_ℓ` be the
     image of `F` in `A_ℓ^×`, the orbit of the configuration `1`. Then `L_F` acts on `O_ℓ` regularly
     (transitively) and `R_F` semiregularly, the two actions commute, and `R_F` acts faithfully on
     `⋃_ℓ O_ℓ`.

   So **two-sided locality holds**: a free lifted group and a transitive transport group, commuting, both
   given by radius-bounded cellular automata on the same periodic data.
3. **Only exact groups.** For every finite ring `R`, every group of invertible linear (additive) cellular
   automata of `R^Z` embeds in `End(R)[t^(±1)]^×`. That group is nilpotent-by-(linear over function fields), hence exact. So
   ring-linear two-sided designs can lift `F_2` (target T1, which would refute (RA_free)), but **never**
   a non-exact group such as Osajda's (target T2). T2 needs two-sided locality that is not linear.
4. **Transports in the loop architecture.**
   - (a) **Level-bounded transports collapse.** In the minimal loop-label designs of
     `loop-labels-reduce-t2-to-two-sided-locality`, suppose the level-`n` transport rule depends only on
     the skeleton's coordinates up to some finite level `N(n)`. Then each level-`n` label layer is a
     minimal equicontinuous factor on which the lifts act by translations. So the commutator subgroup of
     the lifted group acts trivially, and a free lifted group is not faithful.
   - (b) **The escape (design).** Transports must read the colors of **arbitrarily high-level**
     boundaries crossed. Those colors are locally visible, and they make the transport cocycle
     continuous over the tiling but discontinuous over the odometer, at the seams. The label layer is then
     a finite extension of the skeleton that need not be equicontinuous, which is the Sturmian `×_c S_3`
     phenomenon.
   - (c) **Plaquettes (design).** Consistency around each 2×2 block of level-`n` squares is a cocycle
     condition. It holds if horizontal transports depend only on the vertical boundary crossed and vertical
     transports only on the horizontal one, with values in commuting groups. Over `M_4(F_2) = M_2 ⊗ M_2`,
     take `GL_2 ⊗ 1` for horizontal steps and `1 ⊗ GL_2` for vertical ones: both families are
     non-abelian and they commute. The lifts are right multiplications.
   - (d) **Architecture.** This label layer sits **above the proximal skeleton**, not directly over the
     MEF. It is outside the hypotheses of the profinite collapse and of the commutator squeeze, both of
     which concern layers over the MEF. Call it **T1′**. Its minimality, freeness and rigidity are not
     checked.

## Proof

**2(a).** The rules are linear with finitely many nonzero coefficients, so they are cellular automata,
and they commute with the shift. Composition is convolution with matrix coefficients: `L_u L_v x = u(vx)`
and `R_u R_v x = (xv)u`. Commutation is associativity, `u(xv) = (ux)v`. `L_(u^(-1))` inverts `L_u`. If
`L_u` is invertible, its inverse `ι` is a cellular automaton commuting with all `R_v` and with the shift.
Every finitely supported `x` equals `R_x(δ_0 · 1)`, so `ι(x) = R_x(ι(δ_0 · 1)) = w · x` with
`w = ι(δ_0 · 1)`. This holds on a dense set, hence everywhere by continuity, and `ι = L_w` with `wu = 1`
(fix from bh-ref-d).

**2(b).** `SL_2(F_2[t]) ⊆ U` is a nontrivial amalgam (Nagao), so it contains non-abelian free subgroups.
Alternatively, it is a linear group that is not virtually solvable, and the Tits alternative applies.

**2(c).**
- `x ↦ Σ_(i mod ℓ) x_i t^i` identifies period-`ℓ` configurations with `A_ℓ`, and `L_u` and `R_u` with
  left and right multiplication by `u mod (t^ℓ − 1)`.
- Left multiplication by the image `F_ℓ` of `F` on its own orbit `O_ℓ = F_ℓ` is regular. Right
  multiplication by `F_ℓ` preserves `O_ℓ` and commutes with it.
- If `u ≠ 1` in `F`, then `u − 1` has bounded degree, so `u ≢ 1 mod t^ℓ − 1` for large `ℓ`, and `R_u`
  moves the configuration `1`.

**3.**
- *Embedding.* A linear cellular automaton is left convolution by a Laurent polynomial with coefficients
  in `End(R)`. So the group embeds in `End(R)[t^(±1)]^×`, which is `R′[t^(±1)]^×` for the finite ring
  `R′ = End(R)`.
- *Reduction.* Let `J` be the Jacobson radical of `R′`, which is nilpotent. Then `J[t^(±1)]` is a
  nilpotent ideal of `R′[t^(±1)]`, and reduction gives
  `1 → 1 + J[t^(±1)] → R′[t^(±1)]^× → (R′/J)[t^(±1)]^×`, with a nilpotent kernel.
- *Linearity.* `R′/J` is a finite semisimple ring `∏_i M_(n_i)(F_(q_i))`. So the image lies in
  `∏_i GL_(n_i)(F_(q_i)[t^(±1)])`, which is linear over the fields `F_(q_i)(t)`.
- *Exactness.* Linear groups are exact, and an extension of an exact group by a nilpotent (amenable)
  group is exact.

**4(a).**
- *The factor.* Level-boundedness makes the label of the level-`n` square at `v`, relative to the square
  at `0`, a continuous function of the odometer point `ω`, with values in a finite group. So the
  level-`n` label layer is a factor `Y_n` of `Y`, equivariant for the lifts. It is conjugate to the orbit
  closure of a skew product `M ×_c O_n` with `c` continuous and finite-valued.
- *Equicontinuity.* By Theorem 1 of the collapse node (a finite group is profinite), `Y_n` is
  equicontinuous. It is minimal as a factor of `Y`, hence a rotation of a compact abelian group, and its
  automorphisms are translations. So the lifted group acts on every `Y_n` through an abelian group.
- *Conclusion.* Lifts change only labels. On points whose paths are all closed, a configuration is
  determined by the skeleton and all loop labels, so commutators act trivially there. In a minimal `Y` such
  points have dense orbits, and commutators commute with the shifts. So by continuity they act trivially on
  all of `Y` (fix from bh-ref-d). ∎

## Lesson for general BH

**The commuting pair exists, but only for exact groups.**
- Ryan's theorem is about the center of all automorphisms. It does not stop a chosen pair of commuting
  groups of cellular automata.
- Matrix-valued linear automata realize the regular two-sided structure exactly: left and right
  multiplication by Laurent polynomial matrices. That is enough for the free group of T1.
- Every such linear pair lifts only exact groups. So T2, and with it (RA′), needs **non-linear**
  two-sided locality. This matches the earlier infinite-dimensionality requirement from the other side.

**What the data layer must be.**
- Transports must be driven by skeleton features of unbounded level (seam colors), not by finitely many
  hierarchy levels.
- The layer must sit above the proximal skeleton, not over the maximal equicontinuous factor. This is
  where neither the profinite collapse nor the commutator squeeze applies.
