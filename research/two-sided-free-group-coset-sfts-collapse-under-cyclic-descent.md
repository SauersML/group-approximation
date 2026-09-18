---
rg: 2
id: two-sided-free-group-coset-sfts-collapse-under-cyclic-descent
kind: claim
title: Over F_2 × F_2 acting on F_2 two-sidedly, quantum families commute on conjugate-short pairs for free, but any local determinism giving cyclic-length descent forces the subshift to be finite
distinct_from:
  coset-invariant-sft-rigidity-descends-along-double-cosets: that is the general descent criterion; this shows its natural instance over F_2 × F_2 with the diagonal, cyclic length as complexity, applies to no infinite subshift.
  permutive-triangle-sfts-are-quantum-rigid: that is a Z^2 mechanism where determinism is directional (rows determine what lies above), so it coexists with infinite shifts; this shows that two-sided symmetry makes every determinism rule insertable at every cut, which forbids that coexistence.
  f2-groups-have-paradoxical-free-minimal-subshifts: that builds free minimal paradoxical subshifts with no rigidity; this rules out one natural rigidity mechanism over F_2 × F_2.
---

**ESTABLISHED (lane proof, elementary, unreviewed; no priority claimed).** Route:
`two-sided-coset-sft-cyclic-descent-collapse-proof`.

## Setting

- `H = F(a, b)` and `Λ = H × H`, acting on `H` by `(p, q).k = pkq^(-1)`.
  - The stabilizer of `1` is the diagonal `Δ`, and `π(p, q) = pq^(-1)`.
- A **two-sided subshift** `Z ⊆ A^H` is closed and invariant under left and right translation. It is
  the same thing as a coset shift `X_Z` over `Λ`.
- **Pair types.** The type of `(k, k')` is the conjugacy class of `k^(-1)k'`. Its span is the cyclic
  length `ℓ`.
- **Determinism rules.** A *rule* is a pair `(S, φ)`, with `S ⊆ H` finite, `1 ∉ S` and
  `φ : A^S -> A`, such that `z(k) = φ(z|_(kS))` for all `z ∈ Z` and `k ∈ H`.
  - By right invariance each rule also holds in every frame: `z(k) = φ(z|_(k r^(-1) S r))` for all `r`.
- **Cyclic descent (CD).** A finite family of rules has CD if there is `L_0` such that every cyclically
  reduced `w` with `|w| > L_0` has a rotation `w'` and a rule `(S, φ)` with `ℓ(w's) < |w|` for all
  `s ∈ S`.
  - Example: Det_U. Take `S = u^(-1)B_(m-1)` for `u ∈ U`, where `U` meets every directed cycle of the
    de Bruijn graph of reduced words of length `m`.

## Theorem

1. **Free commutation.** In every `D`-quantum family of every two-sided coset shift, `F(k)` and `F(k')`
   commute whenever `ℓ(k^(-1)k') ≤ 2D`. So all conjugates of short elements commute, however far apart.
2. **CD gives rigidity.** If `Z` has a finite family of rules with CD, then `X_Z` is `D`-quantum rigid
   for `D ≥ max(L_0/2, 2 + max |s|, ...)`, by `coset-invariant-sft-rigidity-descends-along-double-cosets`
   with `c = ℓ`.
3. **CD forces finiteness.** If `Z` has a finite family of rules with CD, then `Z` is determined by its
   restriction to a finite ball, so `Z` is finite. Then `F_2 × F_2` does not act freely on `Z`, and `X_Z`
   is not a free SFT.
4. **No classical walls.** Every vertical wall `N(e) × H` and every horizontal wall `H × N(e')` meets
   the fibre over every `k`. So points of `X_Z` agreeing on such a wall are equal.

So 2 is vacuous for infinite `Z`. With complexity `ℓ`, the descent criterion certifies no infinite
two-sided subshift.

## Mechanism of 3

- **Local.** Whether inserting `s` at a cut shortens a word is decided by the `max|s|` letters on each
  side of the cut. So CD is a statement about finitely many local contexts.
- **Acyclic.** A cycle of non-descent contexts would give arbitrarily long cyclic words with no descent.
  So the non-descent contexts form an acyclic graph.
- **Linear words.** Every long *linear* word therefore has an interior cut `v = PQ` with a descent
  context.
- **The frame.** The frame `r = Q` turns the rule's set at `gv` into `gPsQ`, which is shorter than `v`
  for every `s ∈ S`. So a ball of radius `R` determines the ball of radius `R + 1`.

## What survives

- Descent with a complexity other than `ℓ`, where some steps increase cyclic length. It is not excluded.
- Less symmetric coset spaces: point stabilizers that cannot rotate a determining set toward every
  direction, as `Δ` does by conjugation.
- The Cornulier shortcut `finite-double-coset-space-with-free-minimal-coset-sft`.

These are recorded on `f2-times-f2-has-a-quantum-rigid-free-minimal-sft`.

## Lesson for general BH

Rigidity costs symmetry twice.
- A large stabilizer `Δ` collapses pair types, so short-type commutation spreads over whole conjugacy
  classes for free.
- The same stabilizer rotates every determinism rule into every frame. Descent in the natural
  complexity then becomes descent in distance, and the subshift collapses to finitely many points.

Rigid infinite examples such as Ledrappier and the permutive triangles survive only because their
determinism is directional: rows determine what lies above them, not a ball determining everything.
So a quantum-rigid free minimal SFT needs point stabilizers that are large enough to merge pair types,
but that fix a direction, such as an end or a horofunction, along which determinism can run
one-sidedly.
