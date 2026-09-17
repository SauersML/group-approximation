---
rg: 2
id: bernoulli-full-shift-conjugacies-are-base-relabelings
kind: claim
title: Over every group, a conjugacy of full shifts carries a Bernoulli measure only to a relabeled Bernoulli measure
distinct_from:
  bijective-ca-preserve-uniform-bernoulli-measure: that shows a bijective automaton of one full shift fixes the uniform measure; this shows a conjugacy between two full shifts carrying one product measure to another forces the bases to be relabelings, for arbitrary non-uniform bases, via a homoclinic Livsic lemma over every group.
  bernoulli-shift-entropy-classifies-for-every-group: that is the classification for arbitrary measurable isomorphisms, open over nonsofic groups; this settles the class of isomorphisms that are continuous, or have bounded homoclinic propagation, in both directions.
---

**Claim (every countable group `G`).** Let `λ` and `κ` be probability vectors of full
support on finite alphabets `A` and `B`. Let `φ: (A^G, λ^G) → (B^G, κ^G)` be a measure
isomorphism of `G`-actions such that one of the following holds:

- (a) `φ` and `φ^(-1)` agree almost everywhere with continuous maps, that is, with
  cellular automata;
- (b) bounded homoclinic propagation: there are finite sets `F, F'` such that for almost
  every `x`, changing `x` at one coordinate `g` changes `φ(x)` only inside `gF`, and the
  same holds for `φ^(-1)` with `F'`.

Then there is a bijection `π: A → B` with `κ(π(a)) = λ(a)` for every `a`. In particular
`H(λ) = H(κ)`, and no such isomorphism realizes a Bernoulli collapse.

**ESTABLISHED 2026-09-17** by `bernoulli-full-shift-conjugacies-are-base-relabelings-proof`.
The proof is elementary and uses no amenability, soficity or entropy theory. For `G = Z`
the conclusion follows from classical Livšic theory on periodic points. The new ingredient
is a Livšic lemma for locally constant potentials over an arbitrary group. It is proved by
counting occurrences of finite patterns, with no periodic points besides the constants.

**Scope, honestly.**
- If `|A| ≠ |B|` there is no conjugacy at all, since the fixed points are the constants (Step 1
  of the proof). So the uniform pairs `u_2`, `u_3` are excluded for a trivial reason. The content
  is for alphabets of equal size with different, non-uniform weights.
- Over `Z`, isomorphisms with finite expected code lengths preserve `Δ` and its Radon–Nikodym
  cocycle; K. Schmidt (Invent. Math. 76, 1984) turned this into the essential-range invariant used
  in the calibration below. That invariant is `{1}` for every uniform base, so it cannot separate
  `u_2` from `u_3` either.

**Paradigm record.** The object changes from entropy to the Radon–Nikodym cocycle of the
homoclinic relation `Δ`, which is the modular data of the ITPFI factor
`⊗_(g∈G) (M_A, λ)`. Invariants of that cocycle are defined for every group.
- *Calibration.* For `G = Z`, Meshalkin's bases `(1/2, 1/8, 1/8, 1/8, 1/8)` and
  `u_4` have equal entropy and are finitarily isomorphic (Keane–Smorodinsky). They are not
  relabelings, so the claim must fail for finitary codes. It does: the cocycles have
  essential ranges `4^Z` and `{1}`, so no `Δ`-preserving isomorphism exists, and finitary
  codes do not preserve `Δ`.
- *First falsifiable step.* The Livšic lemma in Part 2 of the proof was checked by hand on
  the triangular occurrence system, before the transport argument was written.

**Where the method dies for measurable isomorphisms (dead end for this family).**
1. A general measurable isomorphism, including a finitary one, need not map `Δ` to `Δ`.
   The calibration above gives an explicit equal-entropy example over `Z`. The converse
   direction does hold over every group. Let `φ` be finitary with stopping coding sets
   `R(x)`, so that `φ(x)_e` is determined by `x|_(R(x))`, and assume `E|R| < ∞` in both
   directions.
   - A change at `e` can alter `φ(x)_h` only if `e ∈ hR(h^-1 x)`.
   - By invariance of `μ`, the expected number of such `h` is
     `Σ_h P(h^-1 ∈ R(h^-1 x)) = E|R|`.
   - So propagation is a.e. finite, and `φ` preserves `Δ`.
   Such isomorphisms therefore transport the cocycle, and they land exactly in case 2.
2. Suppose `Δ` is preserved. Then the cocycle is transported automatically, and
   `f = log κ(φ(x)_e) − log λ(x_e)` has vanishing homoclinic sums. But `f` is only
   measurable. Constants already have vanishing homoclinic sums, so the cocycle determines
   the potential only modulo a constant. That constant is `H(λ) − H(κ)`. Part 3 pins it by
   evaluating at a constant configuration, which is a null set. The data of `(Δ, λ^G)`
   without `G` is useless anyway: reindexing `G × {0,1} ≅ G` gives
   `(Δ_λ, λ^G) ≅ (Δ_(λ⊗λ), (λ⊗λ)^G)`, so every invariant of the measured homoclinic
   relation is blind to collapse.
So a collapse `X_h ≅ X_h × X_h` over a nonsofic group must use an isomorphism with
unbounded homoclinic propagation in at least one direction. It cannot be a cellular
automaton or a composition of recodings with bounded windows. Cellular automata here are
not required to be linear, so this is independent of algebraic absorption.
