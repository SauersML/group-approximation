---
rg: 2
id: ledrappier-fl-reduction-review
kind: claim
title: Referee review of e85f22f6f9 — the reduction of algebraic T1 on Ledrappier powers to (FL) is correct (infinite minimal sets project to infinite minimal subsets of X_L, the isogeny and the linear self-joining equations check), so is the Frobenius lemma on regular almost automorphic sets, and infinite subshifts are indeed never distal; a literature check found (FL) neither proved nor refuted, with the nearest known results being the measure analogue (Host–Maass–Martínez) and non-minimal automatic invariant sets (Rowland–Yassawi)
distinct_from:
  algebraic-t1-needs-an-infinite-minimal-subset-of-ledrappier: that is the lane reduction under review; this checks items 1–4 and the non-distality remark.
  ledrappier-shift-has-only-finite-minimal-subsets: that states (FL) as OPEN; this records the literature status and the nearest known theorems.
  hyperbolic-racgs-min-star-order-review: that reviews the RACG node; this reviews the (FL) reduction.
---

**ESTABLISHED (referee bh-ref-c, 2026-09-19; review of the two nodes in e85f22f6f9, lane bh-bq2).** Verdict:
**PASS.** (FL) is correctly labelled **OPEN**. I found no statement of it, or of its negation, in the literature
searched (see the last section).

## Item 1, projection: correct

- **Minimality passes to projections.** Coordinate projections are equivariant, so they map `M` onto minimal
  sets.
- **Some projection is infinite.** If every projection were finite, `M` would lie in a finite product.
- **Conclusion.** (FL) excludes infinite minimal subsets of every `X_L^n`, and so excludes algebraic T1 for every
  `F`, with no measures used.

## Item 2, what the free group adds: correct

- **Infinite rows.** Suppose `π_w(M)` is finite. It is then one periodic orbit inside the `mZ^2`-periodic
  subgroup, which is dual to `A/I_m`, so the characters `cw` with `c ∈ I_m` vanish on `M`. By item 3 of the
  free-distal node (reviewed PASS in `algebraic-t1-free-distal-review`), `cw = 0`, hence `w = 0`.
- **`F`-invariance.** `π_w ∘ γ = π_(γ^T w)`.
- **The isogeny.** `(c, c′) ↦ cw + c′w′` is injective for independent `w, w′`. Its image `L` has full rank, and
  finite index because `A/(c)` is finite. So `P` is onto with finite kernel, and `J = P(M)` is a minimal
  self-joining of `N`.
- **The linear equations.** `π_(cw) = c·π_w`. With `c_0A^2 ⊆ L`, the identity
  `c_0 π_(γ^T w) = a_γ π_w + b_γ π_(w′)` maps `M` onto `c_0 N`.
- **The infinite orbit.** A finite orbit in `P^1(k)` would give a finite-index subgroup fixing a point, hence
  solvable. That is excluded, since `F` is not virtually solvable.

## Item 3 and the equivalent forms of (FL): correct

- **Equivalent forms.** Every closed invariant set contains a minimal subset. So "all minimal sets are finite",
  "every uniformly recurrent point is periodic" and "every nonempty closed invariant set contains a periodic
  point" are equivalent.
- **Sub-SFTs.** The sub-SFT conjecture follows.
- **No 2-power periods.** `X_L` has no nonzero `2^kZ^2`-periodic point, since `s^(2^k) − 1 = t^(2^k)` is a unit.

## Item 4, the Frobenius lemma on regular almost automorphic sets: correct

- **The relation.** `f(z) = x_z(0)` is measurable, and the Ledrappier relation gives `τ_b f = f + τ_a f` almost
  everywhere.
- **Frobenius.** The translation operators commute and act on `F_2`-valued functions, so
  `(τ_b + 1 + τ_a)^(2^k) = τ_(2^k b) + 1 + τ_(2^k a)`.
- **Limits.** Translation is continuous in `L^1`, so every limit `(c, d)` satisfies `τ_d f = f + τ_c f`.
- **Conclusion.** `(c, d) = (0, 0)` gives `f = 0` almost everywhere. Then `x_z = 0` for almost every `z`, so
  `0 ∈ N` and `N = {0}`. This kills regular almost automorphic infinite minimal sets over any `K` in which
  `(0, 0)` is an accumulation point of the doubling orbit, in particular over 2-adic odometers.

## "Subshifts are never distal": correct

- **The argument.** An infinite subshift has, for every `n`, distinct points agreeing on a box of radius `n`.
  Recentre at a nearest disagreement and pass to limits. This gives distinct `x′, y′` that agree on an open
  half-plane, and shifting deep into it makes them close.
- **Conclusion.** So a proximal pair exists, and the system is not distal. This is the standard fact that
  expansive distal systems are finite. Furstenberg's structure theorem for distal systems is therefore unavailable,
  as the node says.
- The remarks on isometric layers are correctly labelled as discussion.

## Is (FL) already known? No statement found

(FL) asks whether every closed set invariant under the shift `σ` and the XOR automaton `Φ = 1 + σ` on `F_2^Z`
contains a periodic point. This is the natural-extension form. I searched the arXiv and the web, and read these
sources at the abstract or HTML level:
- **Measure analogue: known.** For algebraic bipermutative cellular automata, measures invariant under `σ` and
  `Φ`, suitably ergodic and of positive entropy, are Haar measure. References: Host–Maass–Martínez, *Uniform
  Bernoulli measure in dynamics of permutative cellular automata with algebraic local rules* (2003); Sablik,
  *Measure rigidity for algebraic bipermutative cellular automata*, arXiv:math/0510564 (ETDS 2007). This is the
  Rudolph-type analogue, and it has a positive-entropy hypothesis.
- **Non-trivial closed invariant sets: known, minimality not addressed.**
  - Rowland–Yassawi, *Automaticity and invariant measures of linear cellular automata*, arXiv:1811.01256. They
    show that "each automatic spacetime diagram defines a (σ, Φ)-invariant subset", which is nontrivial when the
    initial condition is not eventually periodic. They quote Furstenberg's ×2 ×3 theorem as motivation.
  - Einsiedler 2004, as cited by Rowland–Yassawi: invariant sets and measures of every intermediate entropy.
  - Neither source, in what I read, says whether these sets are minimal, or whether they contain `0` or a periodic
    point.
- **Periodicity results.** Kari–Moutot, arXiv:1806.07107: low-complexity configurations of algebraic subshifts
  are periodic. This is consistent with (FL) but does not decide it.
- **Conclusion.** I found no statement that `X_L` has only finite minimal subsets, and no construction of an
  infinite one. (FL) looks genuinely open, a topological, minimal-set analogue of Furstenberg's theorem. Two
  caveats:
  - I did not read Einsiedler 2004 in full; its title and the citation above are all I saw.
  - I did not read Rowland–Yassawi beyond the ar5iv text.

**Suggested first test for the (FL) lane.** The Rowland–Yassawi sets come from `(−2)`-automatic initial
conditions. Check whether they contain `0`, or some periodic point. The Frobenius identity for 2-power rows
suggests they do, since row `2^k` is `x + σ^(2^k)x` and 2-automatic structure aligns with 2-power shifts. If so,
they are not counterexamples. If some automatic set is minimal and infinite, (FL) is false. In that case the
reduction still stands: algebraic T1 would then live over an infinite minimal subset of `X_L` itself.

## Bottom line

The reduction is correct and removes the free group entirely:
- **If (FL) holds,** algebraic T1 dies on every Ledrappier power.
- **If it fails,** a T1 set needs an infinite minimal `N ⊆ X_L`, together with a minimal self-joining obeying a
  Zariski-dense family of linear equations.

(FL) is not settled in the literature I found. The nearest known theorem is measure rigidity with a
positive-entropy hypothesis.
